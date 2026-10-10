import OAI.Combinatorics.VariableWL.GeneralReduction

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E) (marked : Fin r)

structure RingSystem where
  lists : (b : Fin r → Block (n := n) J) → Set (∀ i, Valuation J marked 1 (b i))
  nonempty : ∀ b, (lists b).Nonempty
  compatible : ∀ b y, y ∈ lists b → ∀ i j, General.Agree J marked ⟨b i,y i⟩ ⟨b j,y j⟩
  transfer : ∀ b y, y ∈ lists b → ∀ c,
    ∃ z ∈ lists c, ∀ i, General.Agree J marked ⟨b i,y i⟩ ⟨c i,z i⟩

abbrev TypeAddress (t : Vertex P E n) :=
  {a : Fin r → Bool // ∀ i, a i ∈ J.labels t i}

def siteRing (t : Vertex P E n) (a : TypeAddress J t) (i : Fin r) : Block (n := n) J :=
  ⟨.inl ⟨i,t,a.val i,a.val (finRotate r i)⟩,a.property i,a.property (finRotate r i)⟩

def leftAddress (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    TypeAddress J (left J.source l) :=
  ⟨a,fun i => J.matches_left l i ⟨ha i,rfl⟩⟩

def rightAddress (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    TypeAddress J (right J.target l) :=
  ⟨fun i => matchOutput J l i (a i),fun i => J.matches_right l i ⟨ha i,rfl⟩⟩

def squareRing (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    (i : Fin r) : Block (n := n) J :=
  ⟨.inr ⟨i,l,a i,a (finRotate r i)⟩,ha i,ha (finRotate r i)⟩

noncomputable def ringSum {t : Vertex P E n} {a : TypeAddress J t}
    (y : ∀ i, Valuation J marked 1 (siteRing J t a i)) : Value J t := ∑ i, (y i).val

def Attained (F : RingSystem J marked (n := n)) (t : Vertex P E n) (a : TypeAddress J t) :
    Set (Value J t) := ringSum J marked '' F.lists (siteRing J t a)

theorem attained_nonempty (F : RingSystem J marked (n := n)) (t : Vertex P E n) (a : TypeAddress J t) :
    (Attained J marked F t a).Nonempty := (F.nonempty _).image _

theorem agree_carries (hr : 2 ≤ r) (hn : 0 < n) {ε ε' : Bit}
    {b c : Block (n := n) J} {y : Valuation J marked ε b} {z : Valuation J marked ε' c}
    (h : General.Agree J marked ⟨b,y⟩ ⟨c,z⟩) {a : Readout r n P E}
    {v w : ReadoutValue J a} (hv : Carries J b.val y.val a v)
    (hw : Carries J c.val z.val a w) : v = w := by
  have hh := h a (carries_hasReadout J hv) (carries_hasReadout J hw)
  exact (readout_eq J hr hn _ hv).symm.trans (hh.trans (readout_eq J hr hn _ hw))

theorem copy_left (hr : 2 ≤ r) (hn : 0 < n) (l : Link E n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) (i : Fin r)
    (y : Valuation J marked 1 (siteRing J _ (leftAddress J l a ha) i))
    (z : Valuation J marked 1 (squareRing J l a ha i))
    (h : General.Agree J marked ⟨_,y⟩ ⟨_,z⟩) : y.val = z.val.1.1 := by
  exact agree_carries J marked hr hn h (a := .inl (squareLeft J ⟨i,l,a i,a (finRotate r i)⟩))
    ⟨rfl,HEq.rfl⟩ (Or.inl ⟨rfl,HEq.rfl⟩)

theorem copy_right (hr : 2 ≤ r) (hn : 0 < n) (l : Link E n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) (i : Fin r)
    (y : Valuation J marked 1 (siteRing J _ (rightAddress J l a ha) i))
    (z : Valuation J marked 1 (squareRing J l a ha i))
    (h : General.Agree J marked ⟨_,y⟩ ⟨_,z⟩) : y.val = z.val.1.2 := by
  exact agree_carries J marked hr hn h (a := .inl (squareRight J ⟨i,l,a i,a (finRotate r i)⟩))
    ⟨rfl,HEq.rfl⟩ (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))

theorem squareRing_vertical (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {z : ∀ i, Valuation J marked 1 (squareRing J l a ha i)} (hz : z ∈ F.lists _)
    (i : Fin r) : (z i).val.2.2 = (z (finRotate r i)).val.2.1 := by
  exact agree_carries J marked hr hn (F.compatible _ z hz i (finRotate r i))
    (a := .inr (squareTop ⟨i,l,a i,a (finRotate r i)⟩))
    (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))
    (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))

theorem squareRing_equation (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {z : ∀ i, Valuation J marked 1 (squareRing J l a ha i)} (hz : z ∈ F.lists _) :
    linkLeft J l (∑ i, (z i).val.1.1) + linkRight J l (∑ i, (z i).val.1.2) = linkConstant J l := by
  have he (i : Fin r) : linkLeft J l (z i).val.1.1 + linkRight J l (z i).val.1.2 +
      (z i).val.2.1 + (z i).val.2.2 = marker marked i * linkConstant J l := by
    have h := (z i).property
    change linkLeft J l (z i).val.1.1 + linkRight J l (z i).val.1.2 +
      (z i).val.2.1 + (z i).val.2.2 = 1 * (marker marked i * linkConstant J l) at h
    simpa only [one_mul] using h
  have hs := congrArg (fun f : Fin r → Bit => ∑ i, f i) (funext he)
  simp only [Finset.sum_add_distrib] at hs
  have hv : (∑ i, (z i).val.2.2) = ∑ i, (z i).val.2.1 := by
    simp_rw [squareRing_vertical J marked hr hn F l a ha hz]
    exact Equiv.sum_comp (finRotate r) (fun i => (z i).val.2.1)
  rw [hv] at hs
  have hm : (∑ i, marker marked i * linkConstant J l) = linkConstant J l := by
    simp [marker]
  rw [hm] at hs
  simpa only [map_sum,add_assoc,CharTwo.add_self_eq_zero,add_zero] using hs

theorem agree_symm {ε ε' : Bit} {v : General.Base (n := n) J marked ε}
    {w : General.Base (n := n) J marked ε'} (h : General.Agree J marked v w) :
    General.Agree J marked w v := fun a hw hv => (h a hv hw).symm

theorem attained_link_forward (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {v : Value J (left J.source l)} (hv : v ∈ Attained J marked F _ (leftAddress J l a ha)) :
    ∃ w ∈ Attained J marked F _ (rightAddress J l a ha),
      linkLeft J l v + linkRight J l w = linkConstant J l := by
  obtain ⟨y,hy,rfl⟩ := hv
  obtain ⟨z,hz,hyz⟩ := F.transfer _ y hy (squareRing J l a ha)
  obtain ⟨w,hw,hzw⟩ := F.transfer _ z hz (siteRing J _ (rightAddress J l a ha))
  refine ⟨ringSum J marked w,⟨w,hw,rfl⟩,?_⟩
  have hl := fun i => copy_left J marked hr hn l a ha i (y i) (z i) (hyz i)
  have hr' := fun i => copy_right J marked hr hn l a ha i (w i) (z i) (agree_symm J marked (hzw i))
  simpa only [ringSum,hl,hr'] using squareRing_equation J marked hr hn F l a ha hz

theorem attained_link_reverse (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a)
    {w : Value J (right J.target l)} (hw : w ∈ Attained J marked F _ (rightAddress J l a ha)) :
    ∃ v ∈ Attained J marked F _ (leftAddress J l a ha),
      linkLeft J l v + linkRight J l w = linkConstant J l := by
  obtain ⟨y,hy,rfl⟩ := hw
  obtain ⟨z,hz,hyz⟩ := F.transfer _ y hy (squareRing J l a ha)
  obtain ⟨w,hw,hzw⟩ := F.transfer _ z hz (siteRing J _ (leftAddress J l a ha))
  refine ⟨ringSum J marked w,⟨w,hw,rfl⟩,?_⟩
  have hr' := fun i => copy_right J marked hr hn l a ha i (y i) (z i) (hyz i)
  have hl := fun i => copy_left J marked hr hn l a ha i (w i) (z i) (agree_symm J marked (hzw i))
  simpa only [ringSum,hl,hr'] using squareRing_equation J marked hr hn F l a ha hz
end VariableWL.Blocks

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E) (marked : Fin r)

theorem affine_of_boundary (a b c d : Bit) (h : a+b=c+d) : a+c=b+d := by
  have ht : (2 : Bit) = 0 := by decide
  linear_combination h+(c-b)*ht

theorem attained_link_images (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    (fun v => linkLeft J l v + leftConstant J l) '' Attained J marked F _ (leftAddress J l a ha) =
    (fun v => linkRight J l v + rightConstant J l) '' Attained J marked F _ (rightAddress J l a ha) := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨w,hw,he⟩ := attained_link_forward J marked hr hn F l a ha hv
    exact ⟨w,hw,(affine_of_boundary _ _ _ _ he).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,he⟩ := attained_link_reverse J marked hr hn F l a ha hw
    exact ⟨v,hv,affine_of_boundary _ _ _ _ he⟩

def realAddress (p : P) (a : ProductImages.Instance.Address r) : TypeAddress J (n := n) (.inl p) :=
  ⟨a,fun _ => Finset.mem_univ _⟩

def internalAddress (e : E) (j : Fin n) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    TypeAddress J (.inr (e,j)) := ⟨a,ha⟩

def realAttained (F : RingSystem J marked (n := n)) (p : P) (a : ProductImages.Instance.Address r) :
    Set (Vec (J.dimension p)) := Attained J marked F (.inl p) (realAddress J p a)

def scalarAttained (F : RingSystem J marked (n := n)) (e : E) (j : Fin n)
    (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) : Set Bit :=
  (fun v => v (0 : Fin 1)) '' Attained J marked F (.inr (e,j)) (internalAddress J e j a ha)

def addressedAttained (F : RingSystem J marked (n := n)) (t : Vertex P E n)
    (a : ProductImages.Instance.Address r) : Set (Value J t) :=
  {v | ∃ h : ∀ i, a i ∈ J.labels t i, v ∈ Attained J marked F t ⟨a,h⟩}

theorem addressedAttained_eq (F : RingSystem J marked (n := n)) (t : Vertex P E n)
    (a : TypeAddress J t) : addressedAttained J marked F t a.val = Attained J marked F t a := by
  ext v
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨a.property,h⟩⟩

theorem dependent_linear_image {A : Type uVariable5} (d : A → ℕ) {i j : A} (he : i = j)
    (L : Vec (d i) →ₗ[Bit] Bit) (Q : ∀ t, Set (Vec (d t))) (c : Bit) :
    (fun v => (cast (congrArg (fun t => Vec (d t) →ₗ[Bit] Bit) he) L) v + c) '' Q j =
      (fun v => L v + c) '' Q i := by
  subst j
  rfl

theorem left_image_evaluation (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) :
    (fun v => linkLeft J l v + leftConstant J l) '' addressedAttained J marked F (left J.source l) a =
    if h : l.2.val = 0 then J.leftForm l.1 '' addressedAttained J marked F (.inl (J.source l.1)) a
    else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val-1,by omega⟩)) a := by
  by_cases hz : l.2.val = 0
  · have he := dependent_linear_image (dimension J) (i := .inl (J.source l.1))
      (j := left J.source l) (by simp only [left,dite_eq_left hz])
      (J.linearLeft l.1) (fun t => addressedAttained J marked F t a) (J.constantLeft l.1)
    simp only [linkLeft,dite_eq_left hz,leftConstant,ite_eq_left hz]
    exact he
  · have he := dependent_linear_image (dimension J) (i := .inr (l.1,⟨l.2.val-1,by omega⟩))
      (j := left J.source l) (by simp only [left,dite_eq_right hz])
      (LinearMap.proj (0 : Fin 1)) (fun t => addressedAttained J marked F t a) 0
    simp only [linkLeft,dite_eq_right hz,leftConstant,ite_eq_right hz,add_zero]
    simp only [add_zero] at he
    exact he

theorem right_image_evaluation (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) :
    (fun v => linkRight J l v + rightConstant J l) '' addressedAttained J marked F (right J.target l) a =
    if h : l.2.val = n then J.rightForm l.1 '' addressedAttained J marked F (.inl (J.target l.1)) a
    else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val,by omega⟩)) a := by
  by_cases hz : l.2.val = n
  · have he := dependent_linear_image (dimension J) (i := .inl (J.target l.1))
      (j := right J.target l) (by simp only [right,dite_eq_left hz])
      (J.linearRight l.1) (fun t => addressedAttained J marked F t a) (J.constantRight l.1)
    simp only [linkRight,dite_eq_left hz,rightConstant,ite_eq_left hz]
    exact he
  · have he := dependent_linear_image (dimension J) (i := .inr (l.1,⟨l.2.val,by omega⟩))
      (j := right J.target l) (by simp only [right,dite_eq_right hz])
      (LinearMap.proj (0 : Fin 1)) (fun t => addressedAttained J marked F t a) 0
    simp only [linkRight,dite_eq_right hz,rightConstant,ite_eq_right hz,add_zero]
    simp only [add_zero] at he
    exact he

theorem wire_images (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (l : Link E n) (a : ProductImages.Instance.Address r) (ha : J.Allowed l.1 a) :
    (if h : l.2.val = 0 then J.leftForm l.1 '' addressedAttained J marked F (.inl (J.source l.1)) a
     else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val-1,by omega⟩)) a) =
    (if h : l.2.val = n then J.rightForm l.1 '' addressedAttained J marked F (.inl (J.target l.1))
        (fun i => matchOutput J l i (a i))
     else (fun v => v (0 : Fin 1)) '' addressedAttained J marked F (.inr (l.1,⟨l.2.val,by omega⟩))
        (fun i => matchOutput J l i (a i))) := by
  rw [← left_image_evaluation J marked F l a,← right_image_evaluation J marked F l]
  exact (congrArg (Set.image _) (addressedAttained_eq J marked F _ (leftAddress J l a ha))).trans
    ((attained_link_images J marked hr hn F l a ha).trans
      (congrArg (Set.image _) (addressedAttained_eq J marked F _ (rightAddress J l a ha))).symm)

theorem attained_first (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    J.leftForm e '' realAttained J marked F (J.source e) a =
      scalarAttained J marked F e ⟨0,hn⟩ a ha := by
  have h := wire_images J marked hr hn F (e,⟨0,by omega⟩) a ha
  simp only [dite_eq_right (Ne.symm hn.ne'),matchOutput,ite_eq_right (Ne.symm hn.ne'),dite_true] at h
  exact (congrArg (Set.image (J.leftForm e)) (addressedAttained_eq J marked F _ (realAddress J (J.source e) a))).symm.trans
    (h.trans (congrArg (Set.image (fun v => v (0 : Fin 1)))
      (addressedAttained_eq J marked F _ (internalAddress J e ⟨0,hn⟩ a ha))))

theorem attained_last (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a) :
    scalarAttained J marked F e ⟨n-1,by omega⟩ a ha =
      J.rightForm e '' realAttained J marked F (J.target e) (J.mapAddress e a) := by
  have h := wire_images J marked hr hn F (e,⟨n,by omega⟩) a ha
  simp only [dite_eq_right hn.ne',matchOutput,dite_true,ite_true] at h
  exact (congrArg (Set.image (fun v => v (0 : Fin 1)))
    (addressedAttained_eq J marked F _ (internalAddress J e ⟨n-1,by omega⟩ a ha))).symm.trans
    (h.trans (congrArg (Set.image (J.rightForm e))
      (addressedAttained_eq J marked F _ (realAddress J (J.target e) (J.mapAddress e a)))))

theorem attained_internal (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n))
    (e : E) (a : ProductImages.Instance.Address r) (ha : J.Allowed e a)
    (j : ℕ) (hj : j+1 < n) :
    scalarAttained J marked F e ⟨j,by omega⟩ a ha =
      scalarAttained J marked F e ⟨j+1,hj⟩ a ha := by
  have h := wire_images J marked hr hn F (e,⟨j+1,by omega⟩) a ha
  simp only [dite_eq_right (Nat.succ_ne_zero j),dite_eq_right hj.ne,matchOutput,ite_eq_right hj.ne] at h
  exact (congrArg (Set.image (fun v => v (0 : Fin 1)))
    (addressedAttained_eq J marked F _ (internalAddress J e ⟨j,by omega⟩ a ha))).symm.trans
    (h.trans (congrArg (Set.image (fun v => v (0 : Fin 1)))
      (addressedAttained_eq J marked F _ (internalAddress J e ⟨j+1,hj⟩ a ha))))

noncomputable def extractedWitness (hr : 2 ≤ r) (hn : 0 < n) (F : RingSystem J marked (n := n)) : J.Witness where
  values := realAttained J marked F
  nonempty p a := attained_nonempty J marked F _ _
  images e a ha := by
    calc
      _ = scalarAttained J marked F e ⟨0,hn⟩ a ha := attained_first J marked hr hn F e a ha
      _ = scalarAttained J marked F e ⟨n-1,by omega⟩ a ha := by
        have hs (j : ℕ) (hj : j < n) : scalarAttained J marked F e ⟨0,hn⟩ a ha =
            scalarAttained J marked F e ⟨j,hj⟩ a ha := by
          induction j with
          | zero => rfl
          | succ j ih => exact (ih (by omega)).trans (attained_internal J marked hr hn F e a ha j hj)
        exact hs _ (by omega)
      _ = _ := attained_last J marked hr hn F e a ha
end VariableWL.Blocks

namespace VariableWL.General
open Blocks VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable6} {E : Type uVariable7} [Fintype P] [Fintype E]
variable (J : ProductImages.Instance r P E) (marked : Fin r)

noncomputable def attainedRings (hr : 3 ≤ r) (hn : 0 < n)
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) (r+1))) :
    RingSystem J marked (n := n) := by
  let query := zeroQuery (n := n) J marked
  let response := fun v : Base (n := n) J marked 1 => valuationQuery J marked v.1 v.2
  let decode := fun b (z : Valuation J marked (n := n) 1 b) => z
  have recognize : ∀ p : Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) (r+1),
      Game.Winning p → ∀ i b w, p i = some (query b,w) → ∃ z : Valuation J marked 1 b, w = response ⟨b,z⟩ :=
    fun p hp i b w hi => zeroQuery_recognized J marked (by omega) hp hi
  have agreement : ∀ p : Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) (r+1),
      Game.Winning p → ∀ i j v w, p i = some (query v.1,response v) → p j = some (query w.1,response w) →
        Agree J marked (Game.decodeSigma decode v) (Game.decodeSigma decode w) := by
    intro p hp i j v w hi hj
    exact zeroQuery_agree J marked hr hn hp hi hj
  exact {
    lists := Game.RingLists query response decode
    nonempty := Game.ringLists_nonempty query response decode recognize hwin
    compatible := fun b y hy i j => Game.ringLists_compatible query response decode (Agree J marked) agreement hy i j
    transfer := fun b y hy c => Game.ringLists_transfer query response decode recognize (Agree J marked) agreement hy c }

theorem consistent_of_winning (hr : 3 ≤ r) (hn : 0 < n)
    (hwin : Game.Winning (fun _ : Fin (r+1) => none :
      Game.Position (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) (r+1))) :
    J.Consistent := ⟨extractedWitness J marked (by omega) hn (attainedRings J marked hr hn hwin)⟩

theorem positive_order [Nonempty P] (ε : Bit) : 0 < (finiteGraph J marked (n := n) ε).order := by
  classical
  obtain ⟨p⟩ := ‹Nonempty P›
  let b := siteRing (n := n) J (.inl p) (realAddress J p (fun _ => false)) marked
  obtain ⟨z,hz⟩ := legal_nonempty J marked ε b.val
  exact Fintype.card_pos_iff.mpr ⟨baseVertex J marked (leafCount J marked) ⟨b,z,hz⟩⟩

theorem equivalent_iff_consistent [Nonempty P] (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1) :
    Equivalent (finiteGraph J marked (n := n) 0) (finiteGraph J marked (n := n) 1) r ↔ J.Consistent := by
  rw [Game.equivalent_iff_winning (by omega) (positive_order J marked 0)]
  exact ⟨consistent_of_winning J marked hr hn,fun ⟨Q⟩ => winning_of_witness J marked hr hn hlarge Q⟩
end VariableWL.General

end OAI
