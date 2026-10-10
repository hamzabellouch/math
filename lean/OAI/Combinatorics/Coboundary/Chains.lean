import Mathlib

namespace OAI

/-!
Augmented F2 simplicial chains, boundaries, exactness, and relative attachments.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains

section
variable {V : Type} [DecidableEq V]
abbrev k := ZMod 2

def rawBoundary : (Finset V →₀ k) →ₗ[k] (Finset V →₀ k) :=
  Finsupp.linearCombination k (fun s => ∑ v ∈ s, Finsupp.single (s.erase v) 1)

@[simp] lemma rawBoundary_single (s : Finset V) (r : k) :
    rawBoundary (Finsupp.single s r) = ∑ v ∈ s, Finsupp.single (s.erase v) r := by
  simp [rawBoundary, Finset.smul_sum]

lemma rawBoundary_squared : (rawBoundary (V := V)).comp rawBoundary = 0 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single, map_sum,
    LinearMap.zero_apply]
  have he : (∑ a ∈ s, ∑ b ∈ s.erase a, Finsupp.single ((s.erase a).erase b) r) =
      ∑ x ∈ s.offDiag, Finsupp.single ((s.erase x.1).erase x.2) r := by
    have hd : s.offDiag = (s ×ˢ s).filter (fun x => x.1 ≠ x.2) := by
      ext x; simp [Finset.mem_offDiag, and_assoc]
    rw [hd, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp [Finset.mem_erase, ne_comm, and_comm]
  rw [he]
  apply Finset.sum_involution (fun x _ => x.swap)
  · intro x hx
    rw [Finset.erase_right_comm]
    ext z
    simp only [Finsupp.add_apply]
    exact CharTwo.add_self_eq_zero _
  · intro x hx _ heq
    exact (Finset.mem_offDiag.mp hx).2.2 (congrArg Prod.fst heq).symm
  · intro x _; exact Prod.swap_swap x
  · intro x hx
    exact Finset.mem_offDiag.mpr ⟨(Finset.mem_offDiag.mp hx).2.1,
      (Finset.mem_offDiag.mp hx).1, (Finset.mem_offDiag.mp hx).2.2.symm⟩

def rawCone (a : V) : (Finset V →₀ k) →ₗ[k] (Finset V →₀ k) :=
  Finsupp.linearCombination k (fun s =>
    if a ∈ s then 0 else Finsupp.single (insert a s) 1)

@[simp] lemma rawCone_single (a : V) (s : Finset V) (r : k) :
    rawCone a (Finsupp.single s r) =
      if a ∈ s then 0 else Finsupp.single (insert a s) r := by
  by_cases h : a ∈ s <;> simp [rawCone, h]

lemma raw_contraction (a : V) :
    rawBoundary.comp (rawCone a) + (rawCone a).comp rawBoundary = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    LinearMap.id_apply, rawCone_single, rawBoundary_single, map_sum]
  by_cases ha : a ∈ s
  · rw [ite_eq_left ha, map_zero, zero_add]
    rw [Finset.sum_eq_single a]
    · simp [Finset.insert_erase ha]
    · intro b hb hba
      simp [Finset.mem_erase, Ne.symm hba, ha]
    · exact fun h => (h ha).elim
  · rw [ite_eq_right ha, rawBoundary_single, Finset.sum_insert ha, Finset.erase_insert ha]
    have he : (∑ b ∈ s, Finsupp.single ((insert a s).erase b) r) =
        ∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.erase_insert_of_ne (show a ≠ b from by intro he; subst b; exact ha hb)]
    rw [he]
    have he' : (∑ b ∈ s, if a ∈ s.erase b then 0 else Finsupp.single (insert a (s.erase b)) r) =
        ∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r := by
      apply Finset.sum_congr rfl
      intro b _
      rw [ite_eq_right (fun h => ha (Finset.mem_of_mem_erase h))]
    rw [he', add_assoc]
    have hz : (∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r) +
        (∑ b ∈ s, Finsupp.single (insert a (s.erase b)) r) = 0 := by
      ext z
      exact CharTwo.add_self_eq_zero _
    rw [hz, add_zero]

structure Complex (V : Type) where
  faces : Set (Finset V)
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V)
abbrev Face (n : ℕ) := {s : Finset V // s ∈ X.faces ∧ s.card = n}
instance (n : ℕ) : DecidableEq (X.Face n) := Classical.decEq _
abbrev Chains (n : ℕ) := X.Face n →₀ k

def erase (n : ℕ) (s : X.Face (n+1)) (v : ↥s.val) : X.Face n :=
  ⟨s.val.erase v.val, X.downward s.property.1 (Finset.erase_subset _ _), by
    rw [Finset.card_erase_of_mem v.property, s.property.2]; omega⟩

def boundary (n : ℕ) : X.Chains (n+1) →ₗ[k] X.Chains n :=
  Finsupp.linearCombination k (fun s => ∑ v : ↥s.val, Finsupp.single (X.erase n s v) 1)

@[simp] lemma boundary_single (n : ℕ) (s : X.Face (n+1)) (r : k) :
    X.boundary n (Finsupp.single s r) = ∑ v : ↥s.val, Finsupp.single (X.erase n s v) r := by
  simp [boundary, Finset.smul_sum]

def embed (n : ℕ) : X.Chains n →ₗ[k] (Finset V →₀ k) := Finsupp.lmapDomain k k Subtype.val

omit [DecidableEq V] in
@[simp] lemma embed_single (n : ℕ) (s : X.Face n) (r : k) :
    X.embed n (Finsupp.single s r) = Finsupp.single s.val r := by
  change Finsupp.mapDomain Subtype.val (Finsupp.single s r) = _
  exact Finsupp.mapDomain_single

omit [DecidableEq V] in
lemma embed_injective (n : ℕ) : Function.Injective (X.embed n) :=
  Finsupp.mapDomain_injective Subtype.val_injective

lemma embed_boundary (n : ℕ) :
    (X.embed n).comp (X.boundary n) = rawBoundary.comp (X.embed (n+1)) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, boundary_single,
    map_sum, embed_single, rawBoundary_single]
  exact Finset.sum_coe_sort s.val (fun v => Finsupp.single (s.val.erase v) r)

@[simp] lemma boundary_squared (n : ℕ) :
    (X.boundary n).comp (X.boundary (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply X.embed_injective n
  change (X.embed n).comp (X.boundary n) (X.boundary (n+1) c) = _
  rw [embed_boundary]
  change rawBoundary ((X.embed (n+1)).comp (X.boundary (n+1)) c) = _
  rw [embed_boundary]
  change rawBoundary.comp rawBoundary (X.embed (n+2) c) = _
  rw [rawBoundary_squared]
  simp

def IsConePoint (a : V) : Prop := ∀ σ ∈ X.faces, insert a σ ∈ X.faces

def cone (a : V) (ha : X.IsConePoint a) (n : ℕ) : X.Chains n →ₗ[k] X.Chains (n+1) :=
  Finsupp.linearCombination k (fun s => if h : a ∈ s.val then 0 else
    Finsupp.single ⟨insert a s.val, ha s.val s.property.1, by
      rw [Finset.card_insert_of_notMem h, s.property.2]⟩ 1)

lemma embed_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.embed (n+1)).comp (X.cone a ha n) = (rawCone a).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, cone,
    Finsupp.linearCombination_single, embed_single, rawCone_single]
  by_cases h : a ∈ s.val
  · rw [dite_eq_left h, smul_zero, map_zero, ite_eq_left h]
  · rw [dite_eq_right h, map_smul, embed_single, ite_eq_right h]
    simp

lemma contraction (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.boundary (n+1)).comp (X.cone a ha (n+1)) +
      (X.cone a ha n).comp (X.boundary n) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply X.embed_injective (n+1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add]
  change (X.embed (n+1)).comp (X.boundary (n+1)) (X.cone a ha (n+1) c) +
    (X.embed (n+1)).comp (X.cone a ha n) (X.boundary n c) = _
  rw [embed_boundary, embed_cone]
  change rawBoundary ((X.embed (n+2)).comp (X.cone a ha (n+1)) c) +
    rawCone a ((X.embed n).comp (X.boundary n) c) = _
  rw [embed_boundary, embed_cone]
  exact LinearMap.congr_fun (raw_contraction a) (X.embed (n+1) c)

lemma boundary_exact_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Function.Exact (X.boundary (n+1)) (X.boundary n) := by
  intro c
  constructor
  · intro hc
    refine ⟨X.cone a ha (n+1) c, ?_⟩
    have hh := LinearMap.congr_fun (X.contraction a ha n) c
    simpa [hc] using hh
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (X.boundary_squared n) b

open CategoryTheory

def chainComplex : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of k (X.Chains (i+1)))
    (fun i => ModuleCat.ofHom (X.boundary (i+1)))
    (fun i => ModuleCat.hom_ext (X.boundary_squared (i+1)))

@[simp] lemma chainComplex_d (n : ℕ) :
    X.chainComplex.d (n+1) n = ModuleCat.ofHom (X.boundary (n+1)) := by
  simp [chainComplex, ChainComplex.of_d]

lemma chainComplex_exactAt_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    X.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (X.chainComplex.d (n+2) (n+1)) (X.chainComplex.d (n+1) n)
  rw [chainComplex_d, chainComplex_d]
  exact (X.boundary_exact_of_cone a ha (n+1))

lemma chainComplex_homology_isZero_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Limits.IsZero (X.chainComplex.homology (n+1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (X.chainComplex_exactAt_of_cone a ha n)

def full (V : Type) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := Set.univ
  empty_mem := Set.mem_univ _
  downward := fun _ _ => Set.mem_univ _

lemma full_isConePoint (a : V) : (full V).IsConePoint a := fun _ _ => Set.mem_univ _

def sumCoefficients (n : ℕ) : X.Chains n →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ => 1)

omit [DecidableEq V] in
@[simp] lemma sumCoefficients_single (n : ℕ) (s : X.Face n) (r : k) :
    X.sumCoefficients n (Finsupp.single s r) = r := by
  simp [sumCoefficients]

omit [DecidableEq V] in
lemma embed_zero (c : X.Chains 0) :
    X.embed 0 c = Finsupp.single ∅ (X.sumCoefficients 0 c) := by
  have hh : X.embed 0 = (Finsupp.lsingle ∅).comp (X.sumCoefficients 0) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, embed_single, sumCoefficients_single]
    have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property.2
    rw [hs]
  exact LinearMap.congr_fun hh c

omit [DecidableEq V] in
lemma sumCoefficients_zero_injective : Function.Injective (X.sumCoefficients 0) := by
  intro c d he
  apply X.embed_injective 0
  rw [embed_zero, embed_zero, he]

lemma augmentation_boundary_zero :
    (X.sumCoefficients 0).comp (X.boundary 0) = X.sumCoefficients 1 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, boundary_single,
    map_sum, sumCoefficients_single]
  simp [s.property.2]

lemma augmentation_boundary :
    (X.sumCoefficients 1).comp (X.boundary 1) = 0 := by
  rw [← augmentation_boundary_zero, LinearMap.comp_assoc, boundary_squared, LinearMap.comp_zero]

lemma augmentation_exact_of_cone (a : V) (ha : X.IsConePoint a) :
    Function.Exact (X.boundary 1) (X.sumCoefficients 1) := by
  intro c
  rw [← X.augmentation_boundary_zero]
  change X.sumCoefficients 0 (X.boundary 0 c) = 0 ↔ _
  rw [← map_zero (X.sumCoefficients 0), X.sumCoefficients_zero_injective.eq_iff]
  exact X.boundary_exact_of_cone a ha 0 c

lemma augmentation_surjective_of_cone (a : V) (ha : X.IsConePoint a) :
    Function.Surjective (X.sumCoefficients 1) := by
  intro r
  let s : X.Face 1 := ⟨{a}, by simpa using ha ∅ X.empty_mem, by simp⟩
  exact ⟨Finsupp.single s r, X.sumCoefficients_single 1 s r⟩

end Complex
end

namespace Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]
abbrev Raw (V : Type) := Finset V →₀ k

def supported (P : Set (Finset V)) : Submodule k (Raw V) :=
  Finsupp.supported k k P

omit [DecidableEq V] in
lemma mem_supported (P : Set (Finset V)) (c : Raw V) :
    c ∈ supported P ↔ ∀ s, c s ≠ 0 → s ∈ P := by
  simp [supported, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff]

lemma single_mem_supported {P : Set (Finset V)} {s : Finset V} (hs : s ∈ P) (a : k) :
    Finsupp.single s a ∈ supported P := by
  rw [mem_supported]
  intro t ht
  by_cases h : s = t
  · simpa [← h] using hs
  · exact (ht (Finsupp.single_eq_of_ne (Ne.symm h))).elim

omit [DecidableEq V] [DecidableEq W] in
lemma map_supported (T : Raw V →ₗ[k] Raw W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, ∀ a : k, T (Finsupp.single s a) ∈ supported Q)
    (c : Raw V) (hc : c ∈ supported P) : T c ∈ supported Q := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro s hs
  exact h s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs)) (c s)

def append (F : Finset W) : Raw V →ₗ[k] Raw (W ⊕ V) :=
  Finsupp.lmapDomain k k (F.disjSum ·)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma append_single (F : Finset W) (s : Finset V) (a : k) :
    append F (Finsupp.single s a) = Finsupp.single (F.disjSum s) a :=
  Finsupp.mapDomain_single

def project (F : Finset W) : Raw (W ⊕ V) →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if s.toLeft = F then Finsupp.single s.toRight 1 else 0)

omit [DecidableEq V] in
@[simp] lemma project_single (F : Finset W) (s : Finset (W ⊕ V)) (a : k) :
    project F (Finsupp.single s a) =
      if s.toLeft = F then Finsupp.single s.toRight a else 0 := by
  by_cases h : s.toLeft = F <;> simp [project, h]

omit [DecidableEq V] in
@[simp] lemma project_append (F : Finset W) :
    (project (V := V) F).comp (append F) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp

lemma project_apply (F : Finset W) (c : Raw (W ⊕ V)) (t : Finset V) :
    project F c t = c (F.disjSum t) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single s a =>
    simp only [project_single]
    by_cases h : s.toLeft = F
    · rw [ite_eq_left h]
      have he : s = F.disjSum t ↔ s.toRight = t := by
        rw [Finset.eq_disjSum_iff]
        simp [h]
      simp only [Finsupp.single_apply, he]
    · rw [ite_eq_right h]
      have he : s ≠ F.disjSum t := by
        intro he
        exact h (by simp [he])
      simp [he]

def joinFaces (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) : Set (Finset (W ⊕ V)) :=
  {s | s.toLeft ⊆ F ∧ s.toRight ∈ O.faces}

def oldFaces (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) : Set (Finset (W ⊕ V)) :=
  {s | s ∈ joinFaces F O ∧ s.toLeft ≠ F}

omit [DecidableEq V] [DecidableEq W] in
lemma joinFaces_downward (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V)
    {s t : Finset (W ⊕ V)} (hs : s ∈ joinFaces F O) (ht : t ⊆ s) :
    t ∈ joinFaces F O :=
  ⟨(Finset.toLeft_subset_toLeft ht).trans hs.1,
    O.downward hs.2 (Finset.toRight_subset_toRight ht)⟩

omit [DecidableEq V] [DecidableEq W] in
lemma oldFaces_downward (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V)
    {s t : Finset (W ⊕ V)} (hs : s ∈ oldFaces F O) (ht : t ⊆ s) :
    t ∈ oldFaces F O := by
  refine ⟨joinFaces_downward F O hs.1 ht, ?_⟩
  intro he
  apply hs.2
  apply Finset.Subset.antisymm hs.1.1
  rw [← he]
  exact Finset.toLeft_subset_toLeft ht

lemma project_eq_zero_iff (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (joinFaces F O)) :
    project F c = 0 ↔ c ∈ supported (oldFaces F O) := by
  rw [mem_supported] at hc ⊢
  constructor
  · intro hz s hs
    refine ⟨hc s hs, ?_⟩
    intro he
    have he' : F.disjSum s.toRight = s := by
      rw [← he, Finset.toLeft_disjSum_toRight]
    have := congrArg (fun b : Raw V => b s.toRight) hz
    rw [project_apply, he'] at this
    exact hs this
  · intro h
    apply Finsupp.ext
    intro t
    rw [project_apply]
    by_contra he
    obtain ⟨_, ht⟩ := h (F.disjSum t) he
    exact ht (by simp)

lemma boundary_supported (P : Set (Finset V))
    (hdown : ∀ {s t}, s ∈ P → t ⊆ s → t ∈ P)
    (c : Raw V) (hc : c ∈ supported P) : rawBoundary c ∈ supported P := by
  apply map_supported rawBoundary P P _ c hc
  intro s hs a
  rw [rawBoundary_single]
  apply Submodule.sum_mem
  intro v hv
  exact single_mem_supported (hdown hs (Finset.erase_subset v s)) a

lemma erase_disjSum_inl (A : Finset W) (B : Finset V) (w : W) :
    (A.disjSum B).erase (.inl w) = (A.erase w).disjSum B := by
  ext (x | x) <;> simp [Finset.mem_erase]

lemma erase_disjSum_inr (A : Finset W) (B : Finset V) (v : V) :
    (A.disjSum B).erase (.inr v) = A.disjSum (B.erase v) := by
  ext (x | x) <;> simp [Finset.mem_erase]

lemma boundary_disjSum_single (A : Finset W) (B : Finset V) (a : k) :
    rawBoundary (Finsupp.single (A.disjSum B) a) =
      (∑ w ∈ A, Finsupp.single ((A.erase w).disjSum B) a) +
      (∑ v ∈ B, Finsupp.single (A.disjSum (B.erase v)) a) := by
  rw [rawBoundary_single, Finset.sum_disjSum]
  simp only [erase_disjSum_inl, erase_disjSum_inr]

lemma project_boundary_single (F : Finset W) (s : Finset (W ⊕ V)) (a : k)
    (hs : s.toLeft ⊆ F) :
    project F (rawBoundary (Finsupp.single s a)) =
      rawBoundary (project F (Finsupp.single s a)) := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
  rw [boundary_disjSum_single, map_add, map_sum, map_sum]
  have hleft : (∑ w ∈ s.toLeft,
      project F (Finsupp.single ((s.toLeft.erase w).disjSum s.toRight) a)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have he : s.toLeft.erase w ≠ F := by
      intro he
      have hf : w ∈ s.toLeft.erase w := he ▸ hs hw
      exact Finset.notMem_erase w s.toLeft hf
    simp [he]
  rw [hleft, zero_add, project_single]
  by_cases he : s.toLeft = F
  · simp only [he, Finset.toLeft_disjSum, Finset.toRight_disjSum, project_single,
      ite_true, rawBoundary_single]
  · simp only [project_single, Finset.toLeft_disjSum, he, ite_false, map_zero,
      Finset.sum_const_zero]

lemma project_boundary (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (joinFaces F O)) :
    project F (rawBoundary c) = rawBoundary (project F c) := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact project_boundary_single F s (c s)
    (((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1)

lemma append_supported (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw V)
    (hc : c ∈ supported O.faces) : append F c ∈ supported (joinFaces F O) := by
  apply map_supported (append F) O.faces (joinFaces F O) _ c hc
  intro s hs a
  rw [append_single]
  apply single_mem_supported
  exact ⟨by simp, by simpa using hs⟩

lemma project_supported (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (joinFaces F O)) : project F c ∈ supported O.faces := by
  apply map_supported (project F) (joinFaces F O) O.faces _ c hc
  intro s hs a
  rw [project_single]
  split_ifs
  · exact single_mem_supported hs.2 a
  · exact Submodule.zero_mem _

def graded (P : Set (Finset V)) (n : ℕ) : Set (Finset V) :=
  {s | s ∈ P ∧ s.card = n}

omit [DecidableEq V] in
lemma supported_mono {P Q : Set (Finset V)} (h : P ⊆ Q) :
    supported P ≤ supported Q := by
  intro c hc
  rw [mem_supported] at hc ⊢
  exact fun s hs => h (hc s hs)

omit [DecidableEq V] in
lemma graded_forget (P : Set (Finset V)) (n : ℕ) :
    supported (graded P n) ≤ supported P :=
  supported_mono (fun _ hs => hs.1)

lemma boundary_graded (P : Set (Finset V))
    (hdown : ∀ {s t}, s ∈ P → t ⊆ s → t ∈ P) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded P (n+1))) :
    rawBoundary c ∈ supported (graded P n) := by
  apply map_supported rawBoundary (graded P (n+1)) (graded P n) _ c hc
  intro s hs a
  rw [rawBoundary_single]
  apply Submodule.sum_mem
  intro v hv
  apply single_mem_supported
  refine ⟨hdown hs.1 (Finset.erase_subset v s), ?_⟩
  rw [Finset.card_erase_of_mem hv, hs.2]
  omega

lemma append_graded (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded O.faces n)) :
    append F c ∈ supported (graded (joinFaces F O) (F.card+n)) := by
  apply map_supported (append F) (graded O.faces n)
    (graded (joinFaces F O) (F.card+n)) _ c hc
  intro s hs a
  rw [append_single]
  apply single_mem_supported
  refine ⟨⟨by simp, by simpa using hs.1⟩, ?_⟩
  simp [hs.2]

lemma project_graded (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (c : Raw (W ⊕ V)) (hc : c ∈ supported (graded (joinFaces F O) (F.card+n))) :
    project F c ∈ supported (graded O.faces n) := by
  rw [mem_supported] at hc ⊢
  intro t ht
  rw [project_apply] at ht
  obtain ⟨hs, hn⟩ := hc (F.disjSum t) ht
  refine ⟨by simpa using hs.2, ?_⟩
  simp only [Finset.card_disjSum] at hn
  omega

def ExactIn (P : Set (Finset V)) (n : ℕ) : Prop :=
  ∀ c ∈ supported (graded P n), rawBoundary c = 0 →
    ∃ b ∈ supported (graded P (n+1)), rawBoundary b = c

theorem relative_filling (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (hO : ExactIn O.faces n)
    (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded (joinFaces F O) (F.card+n)))
    (hδ : rawBoundary c ∈ supported (oldFaces F O)) :
    ∃ b ∈ supported (graded (joinFaces F O) (F.card+n+1)),
      c - rawBoundary b ∈ supported (graded (oldFaces F O) (F.card+n)) := by
  have hc' := graded_forget (joinFaces F O) (F.card+n) hc
  have hδ' := boundary_supported (joinFaces F O) (joinFaces_downward F O) c hc'
  have hz : rawBoundary (project F c) = 0 := by
    rw [← project_boundary F O c hc']
    exact (project_eq_zero_iff F O (rawBoundary c) hδ').mpr hδ
  obtain ⟨b, hb, hbc⟩ := hO (project F c) (project_graded F O n c hc) hz
  have hab : append F b ∈ supported (graded (joinFaces F O) (F.card+n+1)) := by
    simpa [Nat.add_assoc] using append_graded F O (n+1) b hb
  refine ⟨append F b, hab, ?_⟩
  have hDB := boundary_graded (joinFaces F O) (joinFaces_downward F O)
    (F.card+n) (append F b) hab
  have hsub := (supported (graded (joinFaces F O) (F.card+n))).sub_mem hc hDB
  have hsub' := graded_forget (joinFaces F O) (F.card+n) hsub
  have hzero : project F (c - rawBoundary (append F b)) = 0 := by
    rw [map_sub, project_boundary F O (append F b)
      (graded_forget (joinFaces F O) (F.card+n+1) hab)]
    have hep : project F (append F b) = b :=
      congrArg (fun f : Raw V →ₗ[k] Raw V => f b) (project_append F)
    rw [hep, hbc, sub_self]
  have hold := (project_eq_zero_iff F O _ hsub').mp hzero
  rw [mem_supported] at hsub hold ⊢
  exact fun s hs => ⟨hold s hs, (hsub s hs).2⟩

omit [DecidableEq V] [DecidableEq W] in
lemma low_degree_old (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (hn : n < F.card)
    (c : Raw (W ⊕ V)) (hc : c ∈ supported (graded (joinFaces F O) n)) :
    c ∈ supported (graded (oldFaces F O) n) := by
  rw [mem_supported] at hc ⊢
  intro s hs
  obtain ⟨hface, hcard⟩ := hc s hs
  refine ⟨⟨hface, ?_⟩, hcard⟩
  intro he
  have h := Finset.card_toLeft_add_card_toRight (u := s)
  rw [he, hcard] at h
  omega

def RelativeExactIn (P Q : Set (Finset V)) (n : ℕ) : Prop :=
  ∀ c ∈ supported (graded Q n), rawBoundary c ∈ supported P →
    ∃ b ∈ supported (graded Q (n+1)),
      c - rawBoundary b ∈ supported (graded P n)

lemma relativeExactIn_join (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (hO : F.card ≤ n → ExactIn O.faces (n-F.card)) :
    RelativeExactIn (oldFaces F O) (joinFaces F O) n := by
  intro c hc hδ
  by_cases hn : F.card ≤ n
  · have he : F.card + (n-F.card) = n := Nat.add_sub_of_le hn
    simpa only [he] using relative_filling F O (n-F.card) (hO hn) c
      (by simpa only [he] using hc) hδ
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    simpa using (low_degree_old F O n (by omega) c hc)

omit [DecidableEq V] in
lemma finite_stage (P : ℕ → Set (Finset V)) (hP : Monotone P) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded (⋃ m, P m) n)) :
    ∃ m, c ∈ supported (graded (P m) n) := by
  have hdir : Directed (· ⊆ ·) P := fun i j =>
    ⟨max i j, hP (le_max_left i j), hP (le_max_right i j)⟩
  have hs : (c.support : Set (Finset V)) ⊆ ⋃ m, P m := by
    intro s hs
    exact ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1
  obtain ⟨m, hm⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hs
  refine ⟨m, ?_⟩
  rw [mem_supported] at hc ⊢
  exact fun s hs => ⟨hm (Finsupp.mem_support_iff.mpr hs), (hc s hs).2⟩

lemma push_filling (P Q : Set (Finset V)) (n : ℕ)
    (hPQ : RelativeExactIn P Q (n+1))
    (b : Raw V) (hb : b ∈ supported (graded Q (n+1)))
    (hδ : rawBoundary b ∈ supported P) :
    ∃ a ∈ supported (graded P (n+1)), rawBoundary a = rawBoundary b := by
  obtain ⟨e, _, he⟩ := hPQ b hb hδ
  refine ⟨b - rawBoundary e, he, ?_⟩
  rw [map_sub]
  have hh := LinearMap.congr_fun (rawBoundary_squared (V := V)) e
  change rawBoundary (rawBoundary e) = 0 at hh
  rw [hh, sub_zero]

theorem exactIn_initial_of_filtration (P : ℕ → Set (Finset V))
    (hP : Monotone P) (n : ℕ)
    (hstep : ∀ m, RelativeExactIn (P m) (P (m+1)) (n+1))
    (hunion : ExactIn (⋃ m, P m) n) : ExactIn (P 0) n := by
  intro c hc hcz
  have hcu : c ∈ supported (graded (⋃ m, P m) n) :=
    supported_mono (P := graded (P 0) n) (Q := graded (⋃ m, P m) n)
      (fun s hs => ⟨Set.mem_iUnion.mpr ⟨0, hs.1⟩, hs.2⟩) hc
  obtain ⟨b, hb, hbc⟩ := hunion c hcu hcz
  obtain ⟨m, hbm⟩ := finite_stage P hP (n+1) b hb
  have hdesc : ∀ m, ∀ b ∈ supported (graded (P m) (n+1)), rawBoundary b = c →
      ∃ a ∈ supported (graded (P 0) (n+1)), rawBoundary a = c := by
    intro m
    induction m with
    | zero => exact fun b hb hbc => ⟨b, hb, hbc⟩
    | succ m ih =>
      intro b hb hbc
      have hδ : rawBoundary b ∈ supported (P m) := by
        rw [hbc]
        exact supported_mono (hP (Nat.zero_le m)) (graded_forget (P 0) n hc)
      obtain ⟨a, ha, hab⟩ := push_filling (P m) (P (m+1)) n (hstep m) b hb hδ
      exact ih a ha (hab.trans hbc)
  exact hdesc m b hbm hbc

omit [DecidableEq V] in
lemma embed_supported_equiv (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : X.Chains n) :
    X.embed n c = ((Finsupp.supportedEquivFinsupp (R := k)
      (graded X.faces n)).symm c : Raw V) := by
  let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) (graded X.faces n)
  have he : X.embed n = (Finsupp.supported k k (graded X.faces n)).subtype.comp
      e.symm.toLinearMap := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
      CoboundaryExpanders.InfiniteChains.Complex.embed_single]
    exact (Finsupp.supportedEquivFinsupp_symm_single (R := k) (graded X.faces n) s a).symm
  exact LinearMap.congr_fun he c

omit [DecidableEq V] in
lemma embed_mem_graded (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : X.Chains n) :
    X.embed n c ∈ supported (graded X.faces n) := by
  rw [embed_supported_equiv]
  exact ((Finsupp.supportedEquivFinsupp (R := k) (graded X.faces n)).symm c).property

omit [DecidableEq V] in
lemma exists_embed_of_mem_graded (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded X.faces n)) : ∃ b : X.Chains n, X.embed n b = c := by
  let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) (graded X.faces n)
  have hc' : c ∈ Finsupp.supported k k (graded X.faces n) := hc
  refine ⟨e ⟨c, hc'⟩, ?_⟩
  exact (embed_supported_equiv X n _).trans
    (congrArg Subtype.val (e.symm_apply_apply ⟨c, hc'⟩))

lemma exactIn_iff_boundary_exact (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) :
    ExactIn X.faces (n+1) ↔ Function.Exact (X.boundary (n+1)) (X.boundary n) := by
  constructor
  · intro h c
    constructor
    · intro hc
      have hz : rawBoundary (X.embed (n+1) c) = 0 := by
        calc
          rawBoundary (X.embed (n+1) c) = X.embed n (X.boundary n c) :=
            (LinearMap.congr_fun (X.embed_boundary n) c).symm
          _ = 0 := by rw [hc, map_zero]
      obtain ⟨b, hb, hbc⟩ := h _ (embed_mem_graded X (n+1) c) hz
      obtain ⟨a, rfl⟩ := exists_embed_of_mem_graded X (n+2) b hb
      refine ⟨a, X.embed_injective (n+1) ?_⟩
      exact (LinearMap.congr_fun (X.embed_boundary (n+1)) a).trans hbc
    · rintro ⟨b, rfl⟩
      exact LinearMap.congr_fun (X.boundary_squared n) b
  · intro h c hc hz
    obtain ⟨a, rfl⟩ := exists_embed_of_mem_graded X (n+1) c hc
    have ha : X.boundary n a = 0 := by
      apply X.embed_injective n
      rw [map_zero]
      exact (LinearMap.congr_fun (X.embed_boundary n) a).trans hz
    obtain ⟨b, hb⟩ := (h a).mp ha
    refine ⟨X.embed (n+2) b, embed_mem_graded X (n+2) b, ?_⟩
    calc
      rawBoundary (X.embed (n+2) b) = X.embed (n+1) (X.boundary (n+1) b) :=
        (LinearMap.congr_fun (X.embed_boundary (n+1)) b).symm
      _ = X.embed (n+1) a := congrArg (X.embed (n+1)) hb

lemma chainComplex_exactAt_of_exactIn (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (h : ExactIn X.faces (n+2)) : X.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (X.chainComplex.d (n+2) (n+1)) (X.chainComplex.d (n+1) n)
  rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d, CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
  exact (exactIn_iff_boundary_exact X (n+1)).mp h

omit [DecidableEq V] in
lemma split_union (A B : Set (Finset V)) (n : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded (A ∪ B) n)) :
    ∃ a ∈ supported (graded A n), ∃ b ∈ supported (graded B n), c = a+b := by
  classical
  refine ⟨c.filter (· ∈ A), ?_, c.filter (· ∉ A), ?_, ?_⟩
  · rw [mem_supported]
    intro s hs
    have ha : s ∈ A := by
      by_contra hn
      exact hs (Finsupp.filter_apply_neg _ _ hn)
    have hs' : c s ≠ 0 := by simpa [Finsupp.filter_apply, ha] using hs
    exact ⟨ha, ((mem_supported _ c).mp hc s hs').2⟩
  · rw [mem_supported]
    intro s hs
    have ha : s ∉ A := by
      intro hy
      exact hs (by simp [hy])
    have hs' : c s ≠ 0 := by simpa [Finsupp.filter_apply, ha] using hs
    obtain ⟨hAB, hn⟩ := (mem_supported _ c).mp hc s hs'
    exact ⟨hAB.resolve_left ha, hn⟩
  · exact (Finsupp.filter_add_filter_not c (· ∈ A)).symm

lemma boundary_piece_supported (P A B : Set (Finset V))
    (hAB : A ∩ B ⊆ P) (a b : Raw V)
    (ha : rawBoundary a ∈ supported A) (hb : rawBoundary b ∈ supported B)
    (hab : rawBoundary (a+b) ∈ supported P) : rawBoundary a ∈ supported P := by
  rw [mem_supported] at ha hb hab ⊢
  intro s hs
  by_contra hp
  have hz : rawBoundary (a+b) s = 0 := by
    by_contra he
    exact hp (hab s he)
  have hs' : rawBoundary b s ≠ 0 := by
    intro hbz
    rw [map_add, Finsupp.add_apply, hbz, add_zero] at hz
    exact hs hz
  exact hp (hAB ⟨ha s hs, hb s hs'⟩)

lemma relativeExactIn_union (P A B : Set (Finset V)) (n : ℕ)
    (hA : ∀ {s t}, s ∈ A → t ⊆ s → t ∈ A)
    (hB : ∀ {s t}, s ∈ B → t ⊆ s → t ∈ B)
    (hAB : A ∩ B ⊆ P)
    (hPA : RelativeExactIn P A n) (hPB : RelativeExactIn P B n) :
    RelativeExactIn P (A ∪ B) n := by
  intro c hc hδ
  obtain ⟨a, ha, b, hb, rfl⟩ := split_union A B n c hc
  have hda := boundary_supported A hA a (graded_forget A n ha)
  have hdb := boundary_supported B hB b (graded_forget B n hb)
  have had := boundary_piece_supported P A B hAB a b hda hdb hδ
  have hbd : rawBoundary b ∈ supported P := by
    have he : rawBoundary b = rawBoundary (a+b) - rawBoundary a := by
      rw [map_add]; abel
    rw [he]
    exact (supported P).sub_mem hδ had
  obtain ⟨ea, hea, hae⟩ := hPA a ha had
  obtain ⟨eb, heb, hbe⟩ := hPB b hb hbd
  refine ⟨ea+eb, ?_, ?_⟩
  · apply Submodule.add_mem
    · exact supported_mono (P := graded A (n+1)) (Q := graded (A ∪ B) (n+1))
        (fun s hs => ⟨Or.inl hs.1, hs.2⟩) hea
    · exact supported_mono (P := graded B (n+1)) (Q := graded (A ∪ B) (n+1))
        (fun s hs => ⟨Or.inr hs.1, hs.2⟩) heb
  · have he : a+b-rawBoundary (ea+eb) = (a-rawBoundary ea)+(b-rawBoundary eb) := by
      rw [map_add]; abel
    rw [he]
    exact Submodule.add_mem _ hae hbe

lemma relativeExactIn_empty (P : Set (Finset V)) (n : ℕ) :
    RelativeExactIn P ∅ n := by
  intro c hc _
  have hz : c = 0 := by
    ext s
    by_contra hs
    exact ((mem_supported _ c).mp hc s hs).1
  subst c
  exact ⟨0, Submodule.zero_mem _, by simp⟩

lemma relativeExactIn_finite_union {ι : Type*} (P : Set (Finset V))
    (A : ι → Set (Finset V)) (n : ℕ)
    (hA : ∀ i, ∀ {s t}, s ∈ A i → t ⊆ s → t ∈ A i)
    (hAB : ∀ i j, i ≠ j → A i ∩ A j ⊆ P)
    (hPA : ∀ i, RelativeExactIn P (A i) n) (I : Finset ι) :
    RelativeExactIn P (⋃ i ∈ I, A i) n := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using relativeExactIn_empty P n
  | @insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    apply relativeExactIn_union P (A i) (⋃ j ∈ I, A j) n (hA i) _ _ (hPA i) ih
    · intro s t hs ht
      obtain ⟨j, hj, hs⟩ := Set.mem_iUnion₂.mp hs
      exact Set.mem_iUnion₂.mpr ⟨j, hj, hA j hs ht⟩
    · intro s hs
      obtain ⟨j, hj, hjs⟩ := Set.mem_iUnion₂.mp hs.2
      exact hAB i j (by intro he; exact hi (he ▸ hj)) ⟨hs.1, hjs⟩

theorem relativeExactIn_iUnion {ι : Type*} (P : Set (Finset V))
    (A : ι → Set (Finset V)) (n : ℕ)
    (hA : ∀ i, ∀ {s t}, s ∈ A i → t ⊆ s → t ∈ A i)
    (hAB : ∀ i j, i ≠ j → A i ∩ A j ⊆ P)
    (hPA : ∀ i, RelativeExactIn P (A i) n) :
    RelativeExactIn P (⋃ i, A i) n := by
  classical
  intro c hc hδ
  have hs : (c.support : Set (Finset V)) ⊆ ⋃ i, A i := by
    intro s hs
    exact ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1
  obtain ⟨I, hI, hcs⟩ := Set.finite_subset_iUnion c.support.finite_toSet hs
  have hci : c ∈ supported (graded (⋃ i ∈ hI.toFinset, A i) n) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    refine ⟨?_, (hc s hs).2⟩
    simpa only [hI.mem_toFinset] using hcs (Finsupp.mem_support_iff.mpr hs)
  obtain ⟨b, hb, hbc⟩ := relativeExactIn_finite_union P A n hA hAB hPA hI.toFinset c hci hδ
  refine ⟨b, ?_, hbc⟩
  apply supported_mono (P := graded (⋃ i ∈ hI.toFinset, A i) (n+1)) _ hb
  intro s hs
  obtain ⟨i, _, his⟩ := Set.mem_iUnion₂.mp hs.1
  exact ⟨Set.mem_iUnion.mpr ⟨i, his⟩, hs.2⟩

end Attachment
end CoboundaryExpanders.InfiniteChains

end

end OAI
