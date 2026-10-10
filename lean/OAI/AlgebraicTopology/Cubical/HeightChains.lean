import OAI.AlgebraicTopology.Cubical.ArtinChains
import OAI.AlgebraicTopology.Simplicial.Chains

namespace OAI

noncomputable section

open Classical Set

namespace CubicalChains.HeightFiltration
open Classical
variable {G A : Type*} [Group G] [LinearOrder A] (L : SimpleGraph A)
variable (K : SimplicialChains.Contraction L)

def embed (g : G) : SimplicialChains.Chains A →ₗ[ℤ] Chains G A :=
  Finsupp.lmapDomain ℤ ℤ (fun w => (g,w))
omit [Group G] [LinearOrder A] in
@[simp] theorem embed_single (g : G) (w : List A) (n : ℤ) :
    embed g (Finsupp.single w n) = Finsupp.single (g,w) n := by simp [embed]

omit [Group G] [LinearOrder A] in
theorem embed_front (g : G) (a : A) (c : SimplicialChains.Chains A) :
    embed g (SimplicialChains.front a c) = front a (embed g c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

omit [Group G] [LinearOrder A] in
theorem upperTerm_embed (g : G) (w : List A) :
    upperTerm g w = -embed g (SimplicialChains.boundaryTerm w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [upperTerm_cons,SimplicialChains.boundaryTerm_cons,map_sub,embed_single,
      embed_front,ih,map_neg]
    abel

omit [Group G] [LinearOrder A] in
theorem upper_embed (g : G) (c : SimplicialChains.Chains A) :
    upper (embed g c) = -embed g (SimplicialChains.boundary c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]; abel
  | single w n => simp [upperTerm_embed,smul_neg]

def homotopyTerm (h : G → ℤ) (g : G) (w : List A) : Chains G A :=
  if h g < 0 then -embed g (K.homotopy (Finsupp.single w 1)) else 0

def homotopy (h : G → ℤ) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => homotopyTerm L K h p.1 p.2)
omit [Group G] in
@[simp] theorem homotopy_single (h : G → ℤ) (g : G) (w : List A) (n : ℤ) :
    homotopy L K h (Finsupp.single (g,w) n) = n • homotopyTerm L K h g w := by simp [homotopy]

omit [Group G] in
theorem homotopy_embed (h : G → ℤ) (g : G) (c : SimplicialChains.Chains A) :
    homotopy L K h (embed g c) = if h g < 0 then -embed g (K.homotopy c) else 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add,hc,hd]
    split
    · simp_all
      abel
    · simp_all
  | single w n =>
    simp only [embed_single,homotopy_single,homotopyTerm]
    split
    · rw [show Finsupp.single w n = n • Finsupp.single w 1 by simp]
      simp only [map_smul,smul_neg]
    · simp

omit [Group G] in
theorem upper_homotopy (h : G → ℤ) (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) (hg : h g < 0) :
    upper (homotopyTerm L K h g w) + homotopy L K h (upperTerm g w) =
      Finsupp.single (g,w) 1 := by
  simp only [homotopyTerm,ite_eq_left hg,map_neg,upper_embed,upperTerm_embed,homotopy_embed]
  simp only [neg_neg]
  rw [← map_add,K.identity w hw,embed_single]

def above (h : G → ℤ) (k : ℕ) (m : ℤ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ m ≤ h p.1}

omit [Group G] in
theorem above_mono (h : G → ℤ) {k : ℕ} {m n : ℤ} (hmn : m ≤ n) :
    above L h k n ≤ above L h k m := by
  apply Finsupp.supported_mono
  intro p hp
  exact ⟨hp.1,hp.2.1,hmn.trans hp.2.2⟩

omit [Group G] in
theorem embed_supported (h : G → ℤ) (g : G) {k : ℕ} (c : SimplicialChains.Chains A)
    (hc : c ∈ SimplicialChains.chains L k) : embed g c ∈ above L h k (h g) := by
  apply supported_map (embed g) _ _ _ hc
  intro w hw
  rw [embed_single]
  exact Finsupp.single_mem_supported ℤ 1 ⟨hw.1,hw.2,le_refl _⟩

omit [Group G] in
theorem homotopyTerm_above (h : G → ℤ) (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) : homotopyTerm L K h g w ∈ above L h (w.length+1) (h g) := by
  unfold homotopyTerm
  split
  · apply Submodule.neg_mem
    apply embed_supported
    exact K.degree _ _ (Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl⟩)
  · exact Submodule.zero_mem _

omit [Group G] in
theorem homotopy_above (h : G → ℤ) {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : homotopy L K h c ∈ above L h (k+1) m := by
  apply supported_map (homotopy L K h) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [homotopy_single,one_smul]
  have ht := homotopyTerm_above L K h g w hw
  rw [hl] at ht
  exact above_mono L h hh ht


variable (v : A → G) (h : G → ℤ)
variable (hv : ∀ g a, h (g * v a) = h g + 1)

include hv in
theorem lowerTerm_above (g : G) (w : List A) (hw : SimplicialChains.Valid L w) :
    lowerTerm v g w ∈ above L h (w.length-1) (h g+1) := by
  apply Finsupp.supported_mono _ (lowerTerm_supported v g w)
  rintro ⟨g',u⟩ ⟨a,ha,rfl⟩
  exact ⟨SimplicialChains.valid_sublist hw ha.sublist,by have := ha.length; omega,
    by dsimp; rw [hv]⟩

include hv in
theorem lower_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : lower v c ∈ above L h (k-1) (m+1) := by
  apply supported_map (lower v) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [lower_single,one_smul]
  have ht := lowerTerm_above L v h hv g w hw
  rw [hl] at ht
  exact above_mono L h (by omega) ht

omit [Group G] in
theorem upper_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : upper c ∈ above L h (k-1) m := by
  apply supported_map (upper) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  rw [upper_single,one_smul]
  apply Finsupp.supported_mono _ (upperTerm_supported g w)
  rintro ⟨g',u⟩ ⟨rfl,hs,he⟩
  dsimp at hl he hh ⊢
  exact ⟨SimplicialChains.valid_sublist hw hs,by omega,hh⟩

include hv in
theorem boundary_above {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : boundary v c ∈ above L h (k-1) m := by
  have he : boundary v c = lower v c + upper c := by simp [lower]
  rw [he]
  exact Submodule.add_mem _ (above_mono L h (show m ≤ m+1 by omega) (lower_above L v h hv hc))
    (upper_above L h hc)

omit [Group G] in
theorem homotopy_zero {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) :
    homotopy L K h c = 0 := by
  rw [above,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => homotopy L K h c = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,_,hh⟩,rfl⟩
    simp [homotopyTerm,not_lt.mpr hh]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

def push : Chains G A →ₗ[ℤ] Chains G A :=
  LinearMap.id - (boundary v).comp (homotopy L K h) - (homotopy L K h).comp (boundary v)

theorem push_apply (c : Chains G A) : push L K v h c =
    c - boundary v (homotopy L K h c) - homotopy L K h (boundary v c) := rfl

theorem push_single_negative (g : G) (w : List A) (hw : SimplicialChains.Valid L w)
    (hg : h g < 0) : push L K v h (Finsupp.single (g,w) 1) =
      - lower v (homotopyTerm L K h g w) - homotopy L K h (lowerTerm v g w) := by
  have hu := upper_homotopy L K h g w hw hg
  have he : boundary v (homotopyTerm L K h g w) =
      lower v (homotopyTerm L K h g w) + upper (homotopyTerm L K h g w) := by
    simp [lower]
  have he' : boundaryTerm v g w = lowerTerm v g w + upperTerm g w := by simp [lowerTerm]
  simp only [push_apply,homotopy_single,one_smul,boundary_single]
  rw [he,he',map_add,← hu]
  abel

include hv in
theorem push_single_nonnegative (g : G) (w : List A)
    (hw : SimplicialChains.Valid L w) (hg : 0 ≤ h g) :
    push L K v h (Finsupp.single (g,w) 1) = Finsupp.single (g,w) 1 := by
  have hc : Finsupp.single (g,w) (1 : ℤ) ∈ above L h w.length 0 :=
    Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl,hg⟩
  rw [push_apply,homotopy_zero L K h hc,map_zero,
    homotopy_zero L K h (boundary_above L v h hv hc)]
  simp

include hv in
theorem push_above {k N : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ above L h k (-(N+1 : ℕ) : ℤ)) :
    push L K v h c ∈ above L h k (-(N : ℤ)) := by
  apply supported_map (push L K v h) _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh ⊢
  by_cases hg : h g < 0
  · rw [push_single_negative L K v h g w hw hg]
    apply Submodule.sub_mem
    · apply Submodule.neg_mem
      have ht := lower_above L v h hv (homotopyTerm_above L K h g w hw)
      simp only [Nat.add_sub_cancel] at ht
      rw [hl] at ht
      exact above_mono L h (by norm_num at hh ⊢; omega) ht
    · have ht := homotopy_above L K h (lowerTerm_above L v h hv g w hw)
      have he : w.length-1+1=k := by omega
      rw [he] at ht
      exact above_mono L h (by norm_num at hh ⊢; omega) ht
  · rw [push_single_nonnegative L K v h hv g w hw (not_lt.mp hg)]
    exact Finsupp.single_mem_supported ℤ 1 ⟨hw,hl,by change -(N : ℤ) ≤ h g; omega⟩

variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem boundary_squared {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) : boundary v (boundary v c) = 0 := by
  rw [above,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => boundary v (boundary v c) = 0) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
    simp only [boundary_single,one_smul]
    exact boundary_boundaryTerm v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

include comm in
theorem push_boundary {k : ℕ} {m : ℤ} {c : Chains G A}
    (hc : c ∈ above L h k m) (hd : boundary v c ∈ above L h (k-1) 0) :
    boundary v (push L K v h c) = boundary v c := by
  rw [push_apply,map_sub,map_sub,homotopy_zero L K h hd,map_zero,
    boundary_squared L v h comm (homotopy_above L K h hc)]
  simp

include K hv comm in
theorem push_into_halfspace {k : ℕ} (hk : 0 < k) (N : ℕ) (c : Chains G A)
    (hc : c ∈ above L h k (-(N : ℤ)))
    (hd : boundary v c ∈ above L h (k-1) 0) :
    ∃ b ∈ above L h k 0, boundary v b = boundary v c := by
  induction N generalizing c with
  | zero => exact ⟨c,by simpa using hc,rfl⟩
  | succ N ih =>
    have hp := push_above L K v h hv hk hc
    have he := push_boundary L K v h comm hc hd
    obtain ⟨b,hb,hdb⟩ := ih (push L K v h c) hp (by rwa [he])
    exact ⟨b,hb,hdb.trans he⟩



/-- All valid cells of degree k, without a height restriction. -/
def total (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k}

omit [Group G] in
theorem above_total {k : ℕ} {m : ℤ} {c : Chains G A} (hc : c ∈ above L h k m) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

omit [Group G] in
theorem finite_lower_bound {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    ∃ N : ℕ, c ∈ above L h k (-(N : ℤ)) := by
  refine ⟨c.support.sup (fun p => (-h p.1).toNat),?_⟩
  apply (Finsupp.mem_supported ℤ c).mpr
  intro p hp
  have ht := (Finsupp.mem_supported ℤ c).mp hc hp
  have hb := Finset.le_sup (f := fun p => (-h p.1).toNat) hp
  have hi := Int.self_le_toNat (-h p.1)
  exact ⟨ht.1,ht.2,by omega⟩

include K hv comm in
theorem halfspace_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ above L h k 0)
    (hz : boundary v c = 0) :
    ∃ b ∈ above L h (k+1) 0, boundary v b = c := by
  obtain ⟨b,hb,hdb⟩ := exactTotal hk c (above_total L h hc) hz
  obtain ⟨N,hN⟩ := finite_lower_bound L h hb
  obtain ⟨b',hb',hdb'⟩ := push_into_halfspace L K v h hv comm (by omega) N b hN
    (by simpa [hdb] using hc)
  exact ⟨b',hb',hdb'.trans hdb⟩

end CubicalChains.HeightFiltration

namespace CubicalChains.Reflection
open Reorientation
variable {G A B : Type*} [Group G]

def relabel (f : A → B) : Chains G A →ₗ[ℤ] Chains G B :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (p.1,p.2.map f))
omit [Group G] in
@[simp] theorem relabel_single (f : A → B) (g : G) (w : List A) (n : ℤ) :
    relabel f (Finsupp.single (g,w) n) = Finsupp.single (g,w.map f) n := by simp [relabel]
omit [Group G] in
theorem relabel_front (f : A → B) (a : A) (c : Chains G A) :
    relabel f (front a c) = front (f a) (relabel f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p n => rcases p with ⟨g,w⟩; simp

theorem relabel_boundaryTerm (f : A → B) (v : B → G) (g : G) (w : List A) :
    relabel f (boundaryTerm (v ∘ f) g w) = boundaryTerm v g (w.map f) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [relabel_front,ih]

variable (v : A → G)
def letters (w : List A) : List (Signed A) := w.map (fun a => (a,true))
def mirror : Chains G A →ₗ[ℤ] Chains G A :=
  (normalize v).comp (relabel (fun a => (a,true)))

@[simp] theorem mirror_single (g : G) (w : List A) (n : ℤ) :
    mirror v (Finsupp.single (g,w) n) = n • normalTerm v g (letters w) := by
  simp [mirror,letters]

omit [Group G] in
theorem letters_map (w : List A) : (letters w).map Prod.fst = w := by
  simp [letters,List.map_map,Function.comp_def]

omit [Group G] in
theorem letters_sign (w : List A) : sign (letters w) = (-1 : ℤ)^w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [letters,sign,pow_succ,mul_comm] using congrArg (fun n : ℤ => -n) ih

theorem commute_prod (a : A) (w : List A) (hw : ∀ b ∈ w, Commute (v a) (v b)) :
    Commute (v a) (w.map v).prod := by
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact hw b hb

theorem prod_inv (w : List A) (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    (w.map (fun a => (v a)⁻¹)).prod = (w.map v).prod⁻¹ := by
  induction w with
  | nil => simp
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    simp only [List.map_cons,List.prod_cons,ih hw,mul_inv_rev]
    exact (commute_prod v a w ha).inv_left.inv_right.eq

theorem letters_origin (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    origin v g (letters w) = g * (w.map v).prod⁻¹ := by
  induction w generalizing g with
  | nil => simp [letters]
  | cons a w ih =>
    obtain ⟨ha,hw⟩ := List.pairwise_cons.mp hw
    change origin v (g * (v a)⁻¹) (letters w) = g * (v a * (w.map v).prod)⁻¹
    rw [ih _ hw,mul_inv_rev,mul_assoc,(commute_prod v a w ha).inv_left.inv_right.eq]

theorem mirror_single_explicit (g : G) (w : List A) (n : ℤ)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror v (Finsupp.single (g,w) n) =
      n • ((-1 : ℤ)^w.length • Finsupp.single (g*(w.map v).prod⁻¹,w) 1) := by
  rw [mirror_single,normalTerm,letters_sign,letters_origin v g w hw,letters_map]

theorem mirror_boundaryTerm (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror v (boundaryTerm (fun a => (v a)⁻¹) g w) =
      boundary v (normalTerm v g (letters w)) := by
  have he : (fun a => (v a)⁻¹) = step v ∘ (fun a => (a,true)) := rfl
  rw [mirror,LinearMap.comp_apply,he,relabel_boundaryTerm]
  apply normalize_boundaryTerm
  simpa only [List.pairwise_map] using hw

theorem mirror_twice_single (g : G) (w : List A)
    (hw : w.Pairwise (fun a b => Commute (v a) (v b))) :
    mirror (fun a => (v a)⁻¹) (mirror v (Finsupp.single (g,w) 1)) = Finsupp.single (g,w) 1 := by
  rw [mirror_single_explicit v g w 1 hw,one_smul,map_smul,
    mirror_single_explicit _ _ w 1 (hw.imp (fun {_ _} hc => hc.inv_left.inv_right)),one_smul,
    prod_inv v w hw,inv_inv,inv_mul_cancel_right,smul_smul,← mul_pow]
  simp

open HeightFiltration
variable [LinearOrder A] (L : SimpleGraph A)
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))

include comm in
theorem mirror_total {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror v c ∈ total (G := G) L k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl⟩
  rw [mirror_single_explicit v g w 1 (hw.2.imp (fun {_ _} ha => comm _ _ ha)),one_smul]
  exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℤ 1 ⟨hw,hl⟩)

include comm in
theorem mirror_boundary {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror v (boundary (fun a => (v a)⁻¹) c) = boundary v (mirror v c) := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    mirror v (boundary (fun a => (v a)⁻¹) c) = boundary v (mirror v c)) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_⟩,rfl⟩
    simp only [boundary_single,mirror_single,one_smul]
    exact mirror_boundaryTerm v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

include comm in
theorem mirror_twice {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    mirror (fun a => (v a)⁻¹) (mirror v c) = c := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ =>
    mirror (fun a => (v a)⁻¹) (mirror v c) = c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨hw,_⟩,rfl⟩
    exact mirror_twice_single v g w (hw.2.imp (fun {_ _} ha => comm _ _ ha))
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

include comm in
theorem inverse_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ total (G := G) L k)
    (hz : boundary (fun a => (v a)⁻¹) c = 0) :
    ∃ b ∈ total (G := G) L (k+1), boundary (fun a => (v a)⁻¹) b = c := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hm := mirror_total v L comm hc
  have hdz : boundary v (mirror v c) = 0 := by rw [← mirror_boundary v L comm hc,hz,map_zero]
  obtain ⟨b,hb,hdb⟩ := exactTotal hk _ hm hdz
  refine ⟨mirror (fun a => (v a)⁻¹) b,mirror_total _ L hmi hb,?_⟩
  have he := mirror_boundary (fun a => (v a)⁻¹) L hmi hb
  simp only [inv_inv] at he
  rw [← he,hdb,mirror_twice v L comm hc]



variable (h : G → ℤ)
variable (hv : ∀ g a, h (g * v a) = h g + 1)

omit [LinearOrder A] in
include hv in
theorem height_inverse_step (g : G) (a : A) : h (g*(v a)⁻¹) = h g-1 := by
  have he := hv (g*(v a)⁻¹) a
  rw [inv_mul_cancel_right] at he
  omega

omit [LinearOrder A] in
include hv in
theorem height_prod (g : G) (w : List A) : h (g*(w.map v).prod) = h g + w.length := by
  induction w generalizing g with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons,List.prod_cons,← mul_assoc,ih,hv,List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

omit [LinearOrder A] in
include hv in
theorem height_inv_prod (g : G) (w : List A) : h (g*(w.map v).prod⁻¹) = h g-w.length := by
  have he := height_prod v h hv (g*(w.map v).prod⁻¹) w
  rw [inv_mul_cancel_right] at he
  omega

/-- Cubes lying entirely in the nonpositive halfspace. -/
def below (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ h p.1 + k ≤ 0}

omit [Group G] in
theorem below_total {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

include comm hv in
theorem mirror_above_below {k : ℕ} {c : Chains G A}
    (hc : c ∈ above L (fun g => -h g) k 0) : mirror v c ∈ below L h k := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh
  rw [mirror_single_explicit v g w 1 (hw.2.imp (fun {_ _} ha => comm _ _ ha)),one_smul]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  refine ⟨hw,hl,?_⟩
  change h (g*(w.map v).prod⁻¹)+(k:ℤ) ≤ 0
  rw [height_inv_prod v h hv,hl]
  omega

include comm hv in
theorem mirror_below_above {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    mirror (fun a => (v a)⁻¹) c ∈ above L (fun g => -h g) k 0 := by
  apply supported_map _ _ _ _ hc
  rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
  dsimp at hw hl hh
  have hc' := hw.2.imp (fun {_ _} ha => (comm _ _ ha).inv_left.inv_right)
  rw [mirror_single_explicit _ g w 1 hc',one_smul,
    prod_inv v w (hw.2.imp (fun {_ _} ha => comm _ _ ha)),inv_inv]
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported
  refine ⟨hw,hl,?_⟩
  change 0 ≤ -h (g*(w.map v).prod)
  rw [height_prod v h hv,hl]
  omega

include comm hv in
theorem below_boundary {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    boundary v c ∈ below L h (k-1) := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hh : ∀ g a, -h (g*(v a)⁻¹) = -h g+1 := by
    intro g a
    rw [height_inverse_step v h hv]
    omega
  have hm := mirror_below_above v L comm h hv hc
  have hd := boundary_above L (fun a => (v a)⁻¹) (fun g => -h g) hh hm
  have he := mirror_above_below v L comm h hv hd
  rw [mirror_boundary v L comm (above_total L (fun g => -h g) hm)] at he
  have hi := mirror_twice (fun a => (v a)⁻¹) L hmi (below_total L h hc)
  simp only [inv_inv] at hi
  rwa [hi] at he

variable (K : SimplicialChains.Contraction L)
include comm hv K in
theorem below_cycle_bounds
    (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)
    {k : ℕ} (hk : 0 < k) (c : Chains G A) (hc : c ∈ below L h k)
    (hz : boundary v c = 0) :
    ∃ b ∈ below L h (k+1), boundary v b = c := by
  have hmi : ∀ a b, L.Adj a b → Commute ((v a)⁻¹) ((v b)⁻¹) :=
    fun a b ha => (comm a b ha).inv_left.inv_right
  have hh : ∀ g a, -h (g*(v a)⁻¹) = -h g+1 := by
    intro g a
    rw [height_inverse_step v h hv]
    omega
  have hm := mirror_below_above v L comm h hv hc
  have hdz : boundary (fun a => (v a)⁻¹) (mirror (fun a => (v a)⁻¹) c) = 0 := by
    have he := mirror_boundary (fun a => (v a)⁻¹) L hmi (below_total L h hc)
    simp only [inv_inv] at he
    rw [← he,hz,map_zero]
  obtain ⟨b,hb,hdb⟩ := halfspace_cycle_bounds L K (fun a => (v a)⁻¹) (fun g => -h g) hh hmi
    (fun hk c hc hz => inverse_cycle_bounds v L comm exactTotal hk c hc hz) hk _ hm hdz
  refine ⟨mirror v b,mirror_above_below v L comm h hv hb,?_⟩
  rw [← mirror_boundary v L comm (above_total L (fun g => -h g) hb),hdb]
  have hi := mirror_twice (fun a => (v a)⁻¹) L hmi (below_total L h hc)
  simpa only [inv_inv] using hi

end CubicalChains.Reflection

namespace CubicalChains.LevelExact
open HeightFiltration Reflection
variable {G A : Type*} [Group G] [LinearOrder A] (L : SimpleGraph A)
variable (v : A → G) (h : G → ℤ)

def select (P : G × List A → Prop) : Chains G A →ₗ[ℤ] Chains G A :=
  Finsupp.linearCombination ℤ (fun p => if P p then Finsupp.single p 1 else 0)
omit [Group G] [LinearOrder A] in
@[simp] theorem select_single (P : G × List A → Prop) (p : G × List A) (n : ℤ) :
    select P (Finsupp.single p n) = if P p then Finsupp.single p n else 0 := by
  simp only [select,Finsupp.linearCombination_single]
  split <;> simp

omit [Group G] [LinearOrder A] in
theorem select_supported (P : G × List A → Prop) {Q : Set (G × List A)}
    {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c ∈ Finsupp.supported ℤ ℤ {p | p ∈ Q ∧ P p} := by
  apply supported_map _ _ _ _ hc
  intro p hp
  rw [select_single]
  split
  · exact Finsupp.single_mem_supported ℤ 1 ⟨hp,by assumption⟩
  · exact Submodule.zero_mem _

omit [Group G] [LinearOrder A] in
theorem select_eq_self (P : G × List A → Prop) {Q : Set (G × List A)}
    (hQ : ∀ p ∈ Q, P p) {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c = c := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => select P c = c) _ _ _ _ hc
  · rintro _ ⟨p,hp,rfl⟩; simp [hQ p hp]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd]
  · intro n c _ hc; simp only [map_smul,hc]

omit [Group G] [LinearOrder A] in
theorem select_eq_zero (P : G × List A → Prop) {Q : Set (G × List A)}
    (hQ : ∀ p ∈ Q, ¬P p) {c : Chains G A} (hc : c ∈ Finsupp.supported ℤ ℤ Q) :
    select P c = 0 := by
  rw [Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => select P c = 0) _ _ _ _ hc
  · rintro _ ⟨p,hp,rfl⟩; simp [hQ p hp]
  · simp
  · intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
  · intro n c _ hc; simp only [map_smul,hc,smul_zero]

def plus : Chains G A →ₗ[ℤ] Chains G A := select (fun p => 0 ≤ h p.1)
def minus : Chains G A →ₗ[ℤ] Chains G A := select (fun p => h p.1+p.2.length ≤ 0)
def crossPart : Chains G A →ₗ[ℤ] Chains G A := select (fun p => h p.1 < 0 ∧ 0 < h p.1+p.2.length)
def crossing (k : ℕ) : Submodule ℤ (Chains G A) :=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧
    h p.1 < 0 ∧ 0 < h p.1+k}

omit [Group G] in
theorem crossing_total {k : ℕ} {c : Chains G A} (hc : c ∈ crossing L h k) :
    c ∈ total (G := G) L k := by
  apply Finsupp.supported_mono _ hc
  intro p hp
  exact ⟨hp.1,hp.2.1⟩

omit [Group G] in
theorem plus_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    plus h c ∈ above L h k 0 := by
  apply Finsupp.supported_mono _ (select_supported (fun p => 0 ≤ h p.1) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,hp.2⟩

omit [Group G] in
theorem minus_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    minus h c ∈ below L h k := by
  apply Finsupp.supported_mono _ (select_supported (fun p => h p.1+p.2.length ≤ 0) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,by simpa only [hp.1.2] using hp.2⟩

omit [Group G] in
theorem crossPart_mem {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    crossPart h c ∈ crossing L h k := by
  apply Finsupp.supported_mono _
    (select_supported (fun p => h p.1<0 ∧ 0<h p.1+p.2.length) hc)
  intro p hp
  exact ⟨hp.1.1,hp.1.2,hp.2.1,by simpa only [hp.1.2] using hp.2.2⟩

omit [Group G] in
theorem decomposition {k : ℕ} (hk : 0 < k) {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    c = plus h c + minus h c + crossPart h c := by
  rw [total,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction
    (p := fun c _ => c = plus h c + minus h c + crossPart h c) _ _ _ _ hc
  · rintro _ ⟨⟨g,w⟩,⟨_,hl⟩,rfl⟩
    dsimp at hl
    simp only [plus,minus,crossPart,select_single]
    by_cases hg : 0 ≤ h g
    · simp [hg,show ¬h g+(w.length:ℤ) ≤ 0 by omega,not_lt.mpr hg]
    · by_cases hh : h g+(w.length:ℤ) ≤ 0
      · simp [hg,hh,not_lt.mpr hh]
      · simp [hg,hh,not_le.mp hg,not_le.mp hh]
  · simp
  · intro c d _ _ hc hd
    simp only [map_add]
    calc
      c+d = (plus h c + minus h c + crossPart h c) +
          (plus h d + minus h d + crossPart h d) := congrArg₂ (· + ·) hc hd
      _ = _ := by abel
  · intro n c _ hc
    simp only [map_smul]
    simpa only [smul_add] using congrArg (fun z => n • z) hc

omit [Group G] in
theorem plus_self {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) : plus h c = c :=
  select_eq_self _ (fun _ hp => hp.2.2) hc
omit [Group G] in
theorem plus_below_zero {k : ℕ} (hk : 0 < k) {c : Chains G A} (hc : c ∈ below L h k) :
    plus h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp
  have hh := hp.2.2
  omega
omit [Group G] in
theorem crossPart_above_zero {k : ℕ} {c : Chains G A} (hc : c ∈ above L h k 0) :
    crossPart h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp hh
  exact (not_lt.mpr hp.2.2) hh.1
omit [Group G] in
theorem crossPart_below_zero {k : ℕ} {c : Chains G A} (hc : c ∈ below L h k) :
    crossPart h c = 0 := by
  apply select_eq_zero _ _ hc
  intro p hp hh
  have h₁ := hp.2.1
  have h₂ := hp.2.2
  have h₃ := hh.2
  omega
omit [Group G] in
theorem crossPart_self {k : ℕ} {c : Chains G A} (hc : c ∈ crossing L h k) : crossPart h c = c := by
  apply select_eq_self _ _ hc
  intro p hp
  exact ⟨hp.2.2.1,by simpa only [hp.2.1] using hp.2.2.2⟩

omit [Group G] in
theorem crossing_one_zero {c : Chains G A} (hc : c ∈ crossing L h 1) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have h₁ := hp.2.2.1
  have h₂ := hp.2.2.2
  omega

omit [Group G] in
theorem halves_inter_zero {k : ℕ} (hk : 0 < k) {c : Chains G A}
    (hc : c ∈ above L h k 0) (hd : c ∈ below L h k) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have hq := (Finsupp.mem_supported ℤ c).mp hd (Finsupp.mem_support_iff.mpr hn)
  have h₁ := hp.2.2
  have h₂ := hq.2.2
  omega



variable (K : SimplicialChains.Contraction L)
variable (hv : ∀ g a, h (g * v a) = h g + 1)
variable (comm : ∀ a b, L.Adj a b → Commute (v a) (v b))
variable (exactTotal : ∀ {k : ℕ}, 0 < k → ∀ c, c ∈ total (G := G) L k → boundary v c = 0 →
      ∃ b ∈ total (G := G) L (k+1), boundary v b = c)

include hv in
theorem boundary_total {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    boundary v c ∈ total (G := G) L (k-1) := by
  obtain ⟨N,hN⟩ := finite_lower_bound L h hc
  exact above_total L h (boundary_above L v h hv hN)

include comm in
theorem boundary_squared_total (h : G → ℤ) {k : ℕ} {c : Chains G A} (hc : c ∈ total (G := G) L k) :
    boundary v (boundary v c) = 0 := by
  obtain ⟨N,hN⟩ := finite_lower_bound L h hc
  exact boundary_squared L v h comm hN

/-- The connecting boundary on a crossing square is the difference of its two
height-zero vertices. -/
def levelBoundary : Chains G A →ₗ[ℤ] Chains G A :=
  (boundary v).comp ((plus h).comp (boundary v))
omit [LinearOrder A] in
theorem levelBoundary_apply (c : Chains G A) :
    levelBoundary v h c = boundary v (plus h (boundary v c)) := rfl

include hv comm in
theorem levelBoundary_above {c : Chains G A} (hc : c ∈ above L h 2 0) :
    levelBoundary v h c = 0 := by
  rw [levelBoundary_apply,plus_self L h (boundary_above L v h hv hc)]
  exact boundary_squared L v h comm hc

include hv comm in
theorem levelBoundary_below {c : Chains G A} (hc : c ∈ below L h 2) :
    levelBoundary v h c = 0 := by
  rw [levelBoundary_apply,plus_below_zero L h (by decide) (below_boundary v L comm h hv hc),map_zero]

include hv comm in
theorem levelBoundary_crossPart {c : Chains G A} (hc : c ∈ total (G := G) L 2) :
    levelBoundary v h (crossPart h c) = levelBoundary v h c := by
  have he := congrArg (levelBoundary v h) (decomposition L h (by decide) hc)
  simp only [map_add,levelBoundary_above L v h hv comm (plus_mem L h hc),
    levelBoundary_below L v h hv comm (minus_mem L h hc),zero_add] at he
  exact he.symm

include hv comm in
theorem levelBoundary_cross_boundary {c : Chains G A} (hc : c ∈ crossing L h 3) :
    levelBoundary v h (crossPart h (boundary v c)) = 0 := by
  have ht := crossing_total L h hc
  rw [levelBoundary_crossPart L v h hv comm (boundary_total L v h hv ht),
    levelBoundary_apply,boundary_squared_total L v comm h ht,map_zero,map_zero]

include hv comm K exactTotal in
theorem level_cycle_bounds (c : Chains G A) (hc : c ∈ crossing L h 2)
    (hz : levelBoundary v h c = 0) :
    ∃ t ∈ crossing L h 3, crossPart h (boundary v t) = c := by
  have ht := crossing_total L h hc
  have hd := boundary_total L v h hv ht
  have hp := plus_mem L h hd
  have hm := minus_mem L h hd
  have he : boundary v c = plus h (boundary v c) + minus h (boundary v c) := by
    have hh := decomposition L h (by decide) hd
    rw [crossing_one_zero L h (crossPart_mem L h hd),add_zero] at hh
    exact hh
  have hdp : boundary v (plus h (boundary v c)) = 0 := hz
  have hdm : boundary v (minus h (boundary v c)) = 0 := by
    have hh := congrArg (boundary v) he
    rw [boundary_squared_total L v comm h ht,map_add,hdp,zero_add] at hh
    exact hh.symm
  obtain ⟨a,ha,hda⟩ := halfspace_cycle_bounds L K v h hv comm exactTotal (by decide) _ hp hdp
  obtain ⟨b,hb,hdb⟩ := below_cycle_bounds v L comm h hv K exactTotal (by decide) _ hm hdm
  have hab : c-a-b ∈ total (G := G) L 2 := Submodule.sub_mem _
    (Submodule.sub_mem _ ht (above_total L h ha)) (below_total L h hb)
  have hdz : boundary v (c-a-b) = 0 := by
    simp only [map_sub,hda,hdb]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _)))
  obtain ⟨t,ht',hdt⟩ := exactTotal (by decide) _ hab hdz
  refine ⟨crossPart h t,crossPart_mem L h ht',?_⟩
  have hpdt : crossPart h (boundary v (plus h t)) = 0 :=
    crossPart_above_zero L h (boundary_above L v h hv (plus_mem L h ht'))
  have hmdt : crossPart h (boundary v (minus h t)) = 0 :=
    crossPart_below_zero L h (below_boundary v L comm h hv (minus_mem L h ht'))
  have hh := congrArg (fun z => crossPart h (boundary v z)) (decomposition L h (by decide) ht')
  simp only [map_add,hpdt,hmdt,zero_add] at hh
  rw [← hh,hdt,map_sub,map_sub,crossPart_self L h hc,
    crossPart_above_zero L h ha,crossPart_below_zero L h hb,sub_zero,sub_zero]

variable (dim : ∀ w, SimplicialChains.Valid L w → w.length ≤ 3)
include dim in
omit [Group G] in
theorem total_four_zero {c : Chains G A} (hc : c ∈ total (G := G) L 4) : c = 0 := by
  apply Finsupp.ext
  intro p
  by_contra hn
  have hp := (Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
  have hh := dim p.2 hp.1
  have hl := hp.2
  omega

include hv comm K exactTotal dim in
theorem level_boundary_injective (t : Chains G A) (ht : t ∈ crossing L h 3)
    (hz : crossPart h (boundary v t) = 0) : t = 0 := by
  have htt := crossing_total L h ht
  have hd := boundary_total L v h hv htt
  have hp := plus_mem L h hd
  have hm := minus_mem L h hd
  have he : boundary v t = plus h (boundary v t) + minus h (boundary v t) := by
    have hh := decomposition L h (by decide) hd
    rwa [hz,add_zero] at hh
  have hh := congrArg (boundary v) he
  rw [boundary_squared_total L v comm h htt,map_add] at hh
  have hdp : boundary v (plus h (boundary v t)) = 0 := by
    apply halves_inter_zero L h (by decide) (boundary_above L v h hv hp)
    have he' : boundary v (plus h (boundary v t)) = -boundary v (minus h (boundary v t)) := by
      exact eq_neg_of_add_eq_zero_left hh.symm
    rw [he']
    exact Submodule.neg_mem _ (below_boundary v L comm h hv hm)
  have hdm : boundary v (minus h (boundary v t)) = 0 := by simpa only [hdp,zero_add] using hh.symm
  obtain ⟨a,ha,hda⟩ := halfspace_cycle_bounds L K v h hv comm exactTotal (by decide) _ hp hdp
  obtain ⟨b,hb,hdb⟩ := below_cycle_bounds v L comm h hv K exactTotal (by decide) _ hm hdm
  have hab : t-a-b ∈ total (G := G) L 3 := Submodule.sub_mem _
    (Submodule.sub_mem _ htt (above_total L h ha)) (below_total L h hb)
  have hdz : boundary v (t-a-b) = 0 := by
    simp only [map_sub,hda,hdb]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _)))
  obtain ⟨q,hq,hdq⟩ := exactTotal (by decide) _ hab hdz
  rw [total_four_zero L dim hq,map_zero] at hdq
  have hc := congrArg (crossPart h) hdq
  simpa only [map_zero,map_sub,crossPart_self L h ht,crossPart_above_zero L h ha,
    crossPart_below_zero L h hb,sub_zero] using hc.symm

end CubicalChains.LevelExact


end

end OAI
