import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
abbrev Vertex := Fin 3 → ℤ

def step (x : Vertex) (i : Fin 3) : Vertex := Function.update x i (x i+1)

lemma step_apply_same (x : Vertex) (i : Fin 3) : step x i i=x i+1 := by
  simp [step]
lemma step_apply_ne (x : Vertex) {i j : Fin 3} (h : j≠i) : step x i j=x j := by
  simp [step,h]
lemma step_comm (x : Vertex) (i j : Fin 3) : step (step x i) j=step (step x j) i := by
  ext k
  by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [step,Function.update_apply]

variable {A : Type*} [AddCommGroup A]

def cubicalPotential (f : Fin 3 → Vertex → A) (l : ℤ) (x : Vertex) : A :=
  ∑ k∈Finset.range (x 0-l).toNat, f 0 (Function.update x 0 (l+(k:ℤ)))

lemma update_step_zero (x : Vertex) (k : ℤ) :
    Function.update (step x 0) 0 k=Function.update x 0 k := by simp [step]
lemma step_update_zero (x : Vertex) (k : ℤ) :
    step (Function.update x 0 k) 0=Function.update x 0 (k+1) := by simp [step]
lemma update_step_other (x : Vertex) (k : ℤ) {j : Fin 3} (hj : j≠0) :
    Function.update (step x j) 0 k=step (Function.update x 0 k) j := by
  ext i
  by_cases hi : i=0 <;> by_cases hij : i=j <;> simp_all [step,Function.update_apply]

theorem cubicalPotential_step (f : Fin 3 → Vertex → A) (l : ℤ)
    (hl : ∀ i x, x 0≤l → f i x=0)
    (hsq : ∀ i j x, f i x+f j (step x i)=f j x+f i (step x j))
    (x : Vertex) (i : Fin 3) :
    cubicalPotential f l (step x i)-cubicalPotential f l x=f i x := by
  by_cases hi : i=0
  · subst i
    by_cases hx : l≤x 0
    · have hn : (step x 0 0-l).toNat=(x 0-l).toNat+1 := by
        rw [step_apply_same]
        omega
      simp only [cubicalPotential,hn,update_step_zero,Finset.sum_range_succ]
      have hcast : l+((x 0-l).toNat:ℤ)=x 0 := by omega
      rw [hcast,Function.update_eq_self]
      abel
    · have hx' : x 0≤l := by omega
      have hlen : (x 0-l).toNat=0 := by omega
      have hlen' : (step x 0 0-l).toNat=0 := by rw [step_apply_same]; omega
      simp [cubicalPotential,hlen,hlen',hl 0 x hx']
  · have hi0 : 0≠i := Ne.symm hi
    by_cases hx : l≤x 0
    · have hbase : f i (Function.update x 0 l)=0 := hl i _ (by simp)
      have hcast : l+((x 0-l).toNat:ℤ)=x 0 := by omega
      simp only [cubicalPotential,step_apply_ne x hi0,← Finset.sum_sub_distrib]
      calc
        _ = ∑ k∈Finset.range (x 0-l).toNat,
            (f i (Function.update x 0 (l+((k+1:ℕ):ℤ)))-
             f i (Function.update x 0 (l+(k:ℤ)))) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [update_step_other x _ hi]
          have h := hsq 0 i (Function.update x 0 (l+(k:ℤ)))
          rw [step_update_zero] at h
          simp only [Nat.cast_add,Nat.cast_one]
          rw [show l+((k:ℤ)+1)=l+(k:ℤ)+1 by omega]
          exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h.symm)
        _ = f i (Function.update x 0 (l+((x 0-l).toNat:ℤ)))-
            f i (Function.update x 0 (l+(0:ℤ))) := by
          exact Finset.sum_range_sub (fun k : ℕ ↦ f i (Function.update x 0 (l+(k:ℤ)))) _
        _ = f i x := by rw [hcast,add_zero,Function.update_eq_self,hbase,sub_zero]
    · have hlen : (x 0-l).toNat=0 := by omega
      have hx' : x 0≤l := by omega
      simp [cubicalPotential,step_apply_ne x hi0,hlen,hl i x hx']

def nearestStep (x y : Vertex) : Prop :=
  ∃ i : Fin 3, |x i-y i|=1 ∧ ∀ j, j≠i → x j=y j

def starStep (x y : Vertex) : Prop := x≠y ∧ ∀ i, |x i-y i|≤1

lemma nearestStep_symm {x y : Vertex} (h : nearestStep x y) : nearestStep y x := by
  obtain ⟨i,hi,hrest⟩ := h
  exact ⟨i,by simpa only [abs_sub_comm] using hi,fun j hj ↦ (hrest j hj).symm⟩
lemma nearestStep_step (x : Vertex) (i : Fin 3) : nearestStep x (step x i) := by
  refine ⟨i,?_,fun j hj ↦ (step_apply_ne x hj).symm⟩
  rw [step_apply_same]
  norm_num
lemma nearestStep_eq_step {x y : Vertex} (h : nearestStep x y) :
    ∃ i, y=step x i ∨ x=step y i := by
  obtain ⟨i,hi,hrest⟩ := h
  rcases (abs_eq (by norm_num : (0:ℤ)≤1)).mp hi with hp|hm
  · refine ⟨i,Or.inr ?_⟩
    ext j
    by_cases hj : j=i
    · subst j; rw [step_apply_same]; omega
    · rw [step_apply_ne y hj]; exact hrest j hj
  · refine ⟨i,Or.inl ?_⟩
    ext j
    by_cases hj : j=i
    · subst j; rw [step_apply_same]; omega
    · rw [step_apply_ne x hj]; exact (hrest j hj).symm

def withinReach (e : Vertex → Vertex → Prop) (D : Set Vertex) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (fun u v ↦ u∈D ∧ v∈D ∧ e u v) x y

def NNConnected (D : Set Vertex) : Prop :=
  ∀ x∈D, ∀ y∈D, withinReach nearestStep D x y

def starConnected (D : Set Vertex) : Prop :=
  ∀ x∈D, ∀ y∈D, withinReach starStep D x y

def NNComplementComponent (A B : Set Vertex) : Prop :=
  Disjoint A B ∧ NNConnected B ∧
    ∀ x∈B, ∀ y, y∉A → nearestStep x y → y∈B

def nnBoundary (A B : Set Vertex) : Set Vertex :=
  {x | x∈B ∧ ∃ a∈A, nearestStep a x}

lemma boundary_of_cross {A B : Set Vertex} (hB : NNComplementComponent A B)
    {x y : Vertex} (hx : x∈B) (hy : y∉B) (hxy : nearestStep x y) :
    x∈nnBoundary A B := by
  refine ⟨hx,y,?_,nearestStep_symm hxy⟩
  by_contra hya
  exact hy (hB.2.2 x hx y hya hxy)

def unitCube (x : Vertex) : Set Vertex := {y | ∀ i, x i≤y i ∧ y i≤x i+1}

lemma unitCube_self (x : Vertex) : x∈unitCube x := by intro i; omega
lemma unitCube_step (x : Vertex) (i : Fin 3) : step x i∈unitCube x := by
  intro j
  by_cases hj : j=i
  · subst j; rw [step_apply_same]; omega
  · rw [step_apply_ne x hj]; omega
lemma unitCube_step_step (x : Vertex) {i j : Fin 3} (hij : i≠j) :
    step (step x i) j∈unitCube x := by
  intro k
  by_cases hk : k=i
  · subst k
    rw [step_apply_ne _ hij,step_apply_same]
    omega
  · by_cases hkj : k=j
    · subst k
      rw [step_apply_same,step_apply_ne _ hk]
      omega
    · rw [step_apply_ne _ hkj,step_apply_ne _ hk]; omega

lemma unitCube_star {x y z : Vertex} (hy : y∈unitCube x) (hz : z∈unitCube x)
    (hyz : y≠z) : starStep y z := by
  refine ⟨hyz,fun i ↦ abs_le.mpr ?_⟩
  have h := hy i
  have h' := hz i
  constructor <;> omega

def edgeLabel (B S : Set Vertex) (x y : Vertex) : ZMod 2 :=
  (if x∈S then 1 else 0)*(1-if y∈B then 1 else 0)+
  (if y∈S then 1 else 0)*(1-if x∈B then 1 else 0)

def cubeFlag (S : Set Vertex) (x : Vertex) : ZMod 2 :=
  if ∃ y∈S, y∈unitCube x then 1 else 0

def indicatorTwo (B : Set Vertex) (x : Vertex) : ZMod 2 := if x∈B then 1 else 0

lemma edgeLabel_symm (B S : Set Vertex) (x y : Vertex) :
    edgeLabel B S x y=edgeLabel B S y x := by unfold edgeLabel; ring

lemma edgeLabel_zero_of_same {B S : Set Vertex} (hSB : S⊆B) {x y : Vertex}
    (hxy : x∈B ↔ y∈B) : edgeLabel B S x y=0 := by
  by_cases hx : x∈B
  · simp [edgeLabel,hx,hxy.mp hx]
  · have hy : y∉B := fun h ↦ hx (hxy.mpr h)
    have hsx : x∉S := fun h ↦ hx (hSB h)
    have hsy : y∉S := fun h ↦ hy (hSB h)
    simp [edgeLabel,hsx,hsy]

lemma cubeFlag_eq {A B S : Set Vertex} (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) {x y : Vertex}
    (hy : y∈nnBoundary A B) (hyc : y∈unitCube x) :
    cubeFlag S x=indicatorTwo S y := by
  by_cases hys : y∈S
  · simp [cubeFlag,indicatorTwo,hys,show ∃ z∈S,z∈unitCube x from ⟨y,hys,hyc⟩]
  · have he : ¬∃ z∈S,z∈unitCube x := by
      rintro ⟨z,hzs,hzc⟩
      by_cases hzy : z=y
      · exact hys (hzy ▸ hzs)
      · exact hys ((hcoh z (hS hzs) y hy (unitCube_star hzc hyc hzy)).mp hzs)
    simp [cubeFlag,indicatorTwo,hys,he]

lemma edgeLabel_unitCube {A B S : Set Vertex} (hB : NNComplementComponent A B)
    (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) {x u v : Vertex}
    (hu : u∈unitCube x) (hv : v∈unitCube x) (huv : nearestStep u v) :
    edgeLabel B S u v=cubeFlag S x*(indicatorTwo B v-indicatorTwo B u) := by
  have hSB : S⊆B := fun _ hz ↦ (hS hz).1
  by_cases hub : u∈B <;> by_cases hvb : v∈B
  · simp [edgeLabel,indicatorTwo,hub,hvb]
  · have hsv : v∉S := fun h ↦ hvb (hSB h)
    have hf := cubeFlag_eq hS hcoh (boundary_of_cross hB hub hvb huv) hu
    rw [hf]
    by_cases hus : u∈S
    · norm_num [edgeLabel,indicatorTwo,hub,hvb,hsv,hus]
      decide
    · simp [edgeLabel,indicatorTwo,hub,hvb,hsv,hus]
  · have hsu : u∉S := fun h ↦ hub (hSB h)
    have hf := cubeFlag_eq hS hcoh
      (boundary_of_cross hB hvb hub (nearestStep_symm huv)) hv
    rw [hf]
    by_cases hvs : v∈S <;> norm_num [edgeLabel,indicatorTwo,hub,hvb,hsu,hvs]
  · have hsu : u∉S := fun h ↦ hub (hSB h)
    have hsv : v∉S := fun h ↦ hvb (hSB h)
    simp [edgeLabel,indicatorTwo,hub,hvb,hsu,hsv]

lemma edgeLabel_square {A B S : Set Vertex} (hB : NNComplementComponent A B)
    (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) (x : Vertex) (i j : Fin 3) :
    edgeLabel B S x (step x i)+edgeLabel B S (step x i) (step (step x i) j)=
    edgeLabel B S x (step x j)+edgeLabel B S (step x j) (step (step x j) i) := by
  by_cases hij : i=j
  · subst j; rfl
  have htop := unitCube_step_step x hij
  have htop' := unitCube_step_step x (Ne.symm hij)
  rw [edgeLabel_unitCube hB hS hcoh (unitCube_self x) (unitCube_step x i) (nearestStep_step x i),
    edgeLabel_unitCube hB hS hcoh (unitCube_step x i) htop (nearestStep_step _ j),
    edgeLabel_unitCube hB hS hcoh (unitCube_self x) (unitCube_step x j) (nearestStep_step x j),
    edgeLabel_unitCube hB hS hcoh (unitCube_step x j) htop' (nearestStep_step _ i),
    step_comm x i j]
  ring

lemma zmod_two_neg (z : ZMod 2) : -z=z := by fin_cases z <;> rfl

lemma starStep_symm {x y : Vertex} (h : starStep x y) : starStep y x :=
  ⟨Ne.symm h.1,fun i ↦ by simpa only [abs_sub_comm] using h.2 i⟩

lemma withinReach_preserves {D : Set Vertex} {e : Vertex → Vertex → Prop}
    {W : Type*} (q : Vertex → W)
    (hstep : ∀ x∈D, ∀ y∈D, e x y → q x=q y)
    {x y : Vertex} (h : withinReach e D x y) : q x=q y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head h' _ ih => exact (hstep _ h'.1 _ h'.2.1 h'.2.2).trans ih

lemma exists_boundary_potential {A B S : Set Vertex} (hA : A.Finite)
    (hB : NNComplementComponent A B) (hS : S⊆nnBoundary A B)
    (hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S)) :
    ∃ q : Vertex → ZMod 2, ∀ x y, nearestStep x y →
      q y-q x=edgeLabel B S x y := by
  obtain ⟨b,hb⟩ := (hA.image (fun x : Vertex ↦ x 0)).bddBelow
  have hmin (a : Vertex) (ha : a∈A) : b≤a 0 :=
    hb (Set.mem_image_of_mem _ ha)
  let l : ℤ := b-2
  let f : Fin 3 → Vertex → ZMod 2 := fun i x ↦ edgeLabel B S x (step x i)
  have hSB : S⊆B := fun _ hz ↦ (hS hz).1
  have hl : ∀ i x, x 0≤l → f i x=0 := by
    intro i x hx
    have hx0 : x 0<b := by dsimp [l] at hx; omega
    have hs0 : step x i 0<b := by
      by_cases hi : i=0
      · subst i; rw [step_apply_same]; dsimp [l] at hx; omega
      · rw [step_apply_ne x (Ne.symm hi)]; exact hx0
    have hxa : x∉A := fun ha ↦ (not_le.mpr hx0) (hmin x ha)
    have hsa : step x i∉A := fun ha ↦ (not_le.mpr hs0) (hmin _ ha)
    apply edgeLabel_zero_of_same hSB
    exact ⟨fun h ↦ hB.2.2 x h _ hsa (nearestStep_step x i),
      fun h ↦ hB.2.2 _ h x hxa (nearestStep_symm (nearestStep_step x i))⟩
  have hsq : ∀ i j x, f i x+f j (step x i)=f j x+f i (step x j) :=
    fun i j x ↦ edgeLabel_square hB hS hcoh x i j
  refine ⟨cubicalPotential f l,?_⟩
  intro x y hxy
  obtain ⟨i,hi|hi⟩ := nearestStep_eq_step hxy
  · subst y
    exact cubicalPotential_step f l hl hsq x i
  · subst x
    have h := cubicalPotential_step f l hl hsq y i
    calc
      _ = -(cubicalPotential f l (step y i)-cubicalPotential f l y) := by abel
      _ = -edgeLabel B S y (step y i) := by rw [h]
      _ = edgeLabel B S (step y i) y := by rw [zmod_two_neg,edgeLabel_symm]

theorem nnBoundary_starConnected {A B : Set Vertex} (hA : A.Finite)
    (hAc : NNConnected A) (hB : NNComplementComponent A B) :
    starConnected (nnBoundary A B) := by
  intro r hr y hy
  let S : Set Vertex := {z | z∈nnBoundary A B ∧ withinReach starStep (nnBoundary A B) r z}
  have hS : S⊆nnBoundary A B := fun _ hz ↦ hz.1
  have hSB : S⊆B := fun _ hz ↦ hz.1.1
  have hrs : r∈S := ⟨hr,Relation.ReflTransGen.refl⟩
  have hcoh : ∀ u∈nnBoundary A B, ∀ v∈nnBoundary A B,
      starStep u v → (u∈S ↔ v∈S) := by
    intro u hu v hv huv
    exact ⟨fun hs ↦ ⟨hv,hs.2.tail ⟨hu,hv,huv⟩⟩,
      fun hs ↦ ⟨hu,hs.2.tail ⟨hv,hu,starStep_symm huv⟩⟩⟩
  obtain ⟨q,hq⟩ := exists_boundary_potential hA hB hS hcoh
  have hAnotB : ∀ a∈A, a∉B := fun _ ha hb ↦ Set.disjoint_left.mp hB.1 ha hb
  have hAcst : ∀ a∈A, ∀ a'∈A, q a=q a' := by
    intro a ha a' ha'
    apply withinReach_preserves q (D := A) _ (hAc a ha a' ha')
    intro u hu v hv huv
    have he := edgeLabel_zero_of_same hSB (show u∈B ↔ v∈B by
      simp only [hAnotB u hu,hAnotB v hv])
    exact (sub_eq_zero.mp ((hq u v huv).trans he)).symm
  have hBcst : ∀ a∈B, ∀ a'∈B, q a=q a' := by
    intro a ha a' ha'
    apply withinReach_preserves q (D := B) _ (hB.2.1 a ha a' ha')
    intro u hu v hv huv
    have he := edgeLabel_zero_of_same hSB (show u∈B ↔ v∈B by
      simp only [hu,hv])
    exact (sub_eq_zero.mp ((hq u v huv).trans he)).symm
  obtain ⟨a,ha,har⟩ := hr.2
  obtain ⟨a',ha',hay⟩ := hy.2
  have haS : a∉S := fun h ↦ hAnotB a ha (hSB h)
  have ha'S : a'∉S := fun h ↦ hAnotB a' ha' (hSB h)
  have hedge : edgeLabel B S a r=1 := by
    simp [edgeLabel,hrs,haS,hAnotB a ha]
  have hyedge : edgeLabel B S a' y=1 := by
    calc
      _ = q y-q a' := (hq a' y hay).symm
      _ = q r-q a := by rw [hBcst y hy.1 r hr.1,hAcst a' ha' a ha]
      _ = 1 := (hq a r har).trans hedge
  have hys : y∈S := by
    by_contra hys
    simp [edgeLabel,ha'S,hys] at hyedge
  exact hys.2

def avoidingStep (C : Finset Vertex) (x y : Vertex) : Prop :=
  x∉C ∧ y∉C ∧ nearestStep x y

def avoidingReach (C : Finset Vertex) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (avoidingStep C) x y

def exterior (C : Finset Vertex) : Set Vertex :=
  {x | x∉C ∧ Set.Infinite {y | avoidingReach C x y}}

def fill (C : Finset Vertex) : Set Vertex := (exterior C)ᶜ

def exteriorShell (C : Finset Vertex) : Set Vertex :=
  {x | x∈exterior C ∧ ∃ c∈C, starStep c x}

def coordinateBox (C : Finset Vertex) : Set Vertex :=
  {x | ∀ i, (∃ c∈C, c i≤x i) ∧ (∃ c∈C, x i≤c i)}

def coordinateRay (x : Vertex) (i : Fin 3) (d : ℤ) (n : ℕ) : Vertex :=
  fun j ↦ if j=i then x j+d*(n:ℤ) else x j

lemma coordinateRay_zero (x : Vertex) (i : Fin 3) (d : ℤ) :
    coordinateRay x i d 0=x := by ext j; simp [coordinateRay]

lemma coordinateRay_injective (x : Vertex) (i : Fin 3) (d : ℤ) (hd : d≠0) :
    Function.Injective (coordinateRay x i d) := by
  intro m n h
  have hv := congrFun h i
  simp only [coordinateRay, ite_true] at hv
  have : (m:ℤ)=(n:ℤ) := mul_left_cancel₀ hd (add_left_cancel hv)
  exact_mod_cast this

lemma coordinateRay_step (x : Vertex) (i : Fin 3) (d : ℤ) (hd : |d|=1) (n : ℕ) :
    nearestStep (coordinateRay x i d n) (coordinateRay x i d (n+1)) := by
  refine ⟨i, ?_, ?_⟩
  · simp only [coordinateRay, ite_true, Nat.cast_add, Nat.cast_one]
    have he : x i+d*(n:ℤ)-(x i+d*((n:ℤ)+1)) = -d := by ring
    rw [he, abs_neg, hd]
  · intro j hj
    simp only [coordinateRay, ite_eq_right hj]

lemma coordinateRay_reachable (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) (n : ℕ) :
    avoidingReach C x (coordinateRay x i d n) := by
  induction n with
  | zero => rw [coordinateRay_zero]; exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail ⟨hC n, hC (n+1), coordinateRay_step x i d hd n⟩

lemma coordinateRay_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) : x∈exterior C := by
  have hd0 : d≠0 := by intro h; simp [h] at hd
  refine ⟨by simpa only [coordinateRay_zero] using hC 0, ?_⟩
  have hi := Set.infinite_range_of_injective (coordinateRay_injective x i d hd0)
  exact hi.mono (by
    rintro y ⟨n,rfl⟩
    exact coordinateRay_reachable C x i d hd hC n)

lemma upper_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, c i<x i) : x∈exterior C := by
  apply coordinateRay_exterior C x i 1 (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, one_mul] at h
  omega

end HardSphere.Lattice
end
end
end
end

end OAI
