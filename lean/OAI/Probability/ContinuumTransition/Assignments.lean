import OAI.Probability.ContinuumTransition.PairEnergy

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section Assignments
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

def assignmentRegion (B : ι → Set X) (e : Equiv.Perm ι) : Set (ι → X) :=
  {x | ∀ i, x i ∈ B (e i)}

omit [DecidableEq ι] in
theorem measurableSet_assignmentRegion {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (e : Equiv.Perm ι) : MeasurableSet (assignmentRegion B e) := by
  convert MeasurableSet.iInter (fun i => (hB (e i)).preimage (measurable_pi_apply i)) using 1
  ext x
  simp [assignmentRegion]

omit [MeasurableSpace X] in
theorem assignmentRegion_pairwiseDisjoint {B : ι → Set X}
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Pairwise (fun e f : Equiv.Perm ι => Disjoint (assignmentRegion B e) (assignmentRegion B f)) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hne : ∃ i, e i ≠ f i := by
    by_contra! h
    exact hef (Equiv.ext h)
  obtain ⟨i, hi⟩ := hne
  exact Set.disjoint_left.mp (hB hi) (hx i) (hy i)

theorem measure_assignment_union (μ : Measure X) [SigmaFinite μ] {B : ι → Set X}
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (Measure.pi (fun _ : ι => μ)) (⋃ e : Equiv.Perm ι, assignmentRegion B e) =
      (Fintype.card ι).factorial * ∏ i, μ (B i) := by
  rw [measure_iUnion (assignmentRegion_pairwiseDisjoint hd)
    (measurableSet_assignmentRegion hB), tsum_fintype]
  have hh (e : Equiv.Perm ι) :
      (Measure.pi (fun _ : ι => μ)) (assignmentRegion B e) = ∏ i, μ (B i) := by
    have heq : assignmentRegion B e = Set.univ.pi (fun i => B (e i)) := by
      ext x
      simp [assignmentRegion]
    rw [heq, Measure.pi_pi, Equiv.prod_comp e (fun i => μ (B i))]
  simp_rw [hh]
  simp [Fintype.card_perm]

theorem integral_lower_of_disjoint_assignments (μ : Measure X) [SigmaFinite μ]
    {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hfinite : ∀ i, μ (B i) ≠ ⊤) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x) {c : ℝ}
    (hinc : ∀ e, assignmentRegion B e ⊆ Ω)
    (hbound : ∀ e, ∀ x ∈ assignmentRegion B e, c ≤ F x) :
    (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let S := ⋃ e : Equiv.Perm ι, assignmentRegion B e
  have hS : MeasurableSet S := MeasurableSet.iUnion (measurableSet_assignmentRegion hB)
  have hsub : S ⊆ Ω := iUnion_subset hinc
  have hmass := measure_assignment_union μ hB hd
  have hSfin : (Measure.pi (fun _ : ι => μ)) S ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top (fun i _ => hfinite i))
  have hconst : IntegrableOn (fun _ : ι → X => c) S (Measure.pi (fun _ : ι => μ)) :=
    integrableOn_const hSfin
  have hle : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
    apply setIntegral_mono_on hconst (hF.mono_set hsub) hS
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    exact hbound e x he
  have hle' := setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)
  have hval : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c := by
    rw [setIntegral_const, Measure.real, hmass, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_prod, smul_eq_mul]
  rw [hval] at hle
  exact hle.trans hle'

omit [DecidableEq ι] in

theorem setIntegral_coordinatePerm (μ : Measure X) [SigmaFinite μ]
    (e : Equiv.Perm ι) (S : Set (ι → X)) (F : (ι → X) → ℝ)
    (hsym : ∀ x, F (x ∘ e) = F x) :
    (∫ x in {x | (x ∘ e) ∈ S}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let p : (ι → X) ≃ᵐ (ι → X) := MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm
  have hpx (x : ι → X) : p x = x ∘ e := by
    ext i
    simpa only [p, Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => X) x (e i))
  have hp : MeasurePreserving p (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : ι => μ)) := measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding F S
  simpa only [hpx, hsym, Set.preimage] using heq

def binaryRegion (A B : Set X) (s : Finset ι) : Set (ι → X) :=
  {x | ∀ i, if i ∈ s then x i ∈ A else x i ∈ B}

theorem measurableSet_binaryRegion {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (s : Finset ι) : MeasurableSet (binaryRegion A B s) := by
  have hh (i : ι) : MeasurableSet ((fun x : ι → X => x i) ⁻¹' (if i ∈ s then A else B)) := by
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using hA.preimage (measurable_pi_apply i)
    · simpa only [ite_eq_right hi] using hB.preimage (measurable_pi_apply i)
  convert MeasurableSet.iInter hh using 1
  ext x
  simp only [binaryRegion, mem_ofPred_eq, mem_iInter, mem_preimage]
  apply forall_congr'
  intro i
  split_ifs <;> rfl

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_pairwiseDisjoint {A B : Set X} (hd : Disjoint A B) :
    Pairwise (fun s t : Finset ι => Disjoint (binaryRegion A B s) (binaryRegion A B t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hst
  ext i
  constructor
  · intro hi
    by_contra ht
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i)
      (by simpa only [ite_eq_right ht] using hy i)
  · intro hi
    by_contra hs
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hy i)
      (by simpa only [ite_eq_right hs] using hx i)

theorem setIntegral_binaryRegion_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} {s t : Finset ι} (hst : s.card = t.card) (F : (ι → X) → ℝ)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x) :
    (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hmem (i : ι) : e i ∈ t ↔ i ∈ s := by
    rw [← he]
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact e.injective hji ▸ hj
    · exact fun hi => ⟨i, hi, rfl⟩
  have hpre : {x : ι → X | (x ∘ e) ∈ binaryRegion A B s} = binaryRegion A B t := by
    ext x
    change (∀ i, if i ∈ s then x (e i) ∈ A else x (e i) ∈ B) ↔
      (∀ i, if i ∈ t then x i ∈ A else x i ∈ B)
    simp_rw [← hmem]
    constructor
    · intro hh j
      obtain ⟨i, rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  have hh := setIntegral_coordinatePerm μ e (binaryRegion A B s) F (hsym e)
  rw [hpre] at hh
  exact hh.symm

theorem integral_lower_binary_assignments (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω) :
    (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  classical
  let T := (Finset.univ : Finset ι).powersetCard s.card
  have hcard (t : Finset ι) (ht : t ∈ T) : t.card = s.card := (Finset.mem_powersetCard.mp ht).2
  have hsub : (⋃ t ∈ T, binaryRegion A B t) ⊆ Ω := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
    exact hinc t (hcard t ht) hx
  have hh := integral_biUnion_finset T (fun t _ => measurableSet_binaryRegion hA hB t)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun t ht => hF.mono_set (hinc t (hcard t ht)))
  have hEq : (∫ x in ⋃ t ∈ T, binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) := by
    rw [hh]
    calc
      _ = ∑ _t ∈ T, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_binaryRegion_eq μ (hcard t ht) F hsym
      _ = _ := by simp [T]
  rw [← hEq]
  exact setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)

theorem setIntegral_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    (f : ({i : ι // i ∈ s} → X) → ℝ) (g : ({i : ι // i ∉ s} → X) → ℝ) :
    (∫ x in binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i)
      ∂(Measure.pi (fun _ : ι => μ))) =
    (∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
    (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
      ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding
    (fun z => f z.1 * g z.2) (SA ×ˢ SB)
  rw [hpre, setIntegral_prod_mul] at heq
  exact heq

theorem integrableOn_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) :
    IntegrableOn (fun x : ι → X =>
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i))
      (binaryRegion A B s) (Measure.pi (fun _ : ι => μ)) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have hprod : IntegrableOn (fun z => f z.1 * g z.2) (SA ×ˢ SB)
      ((Measure.pi (fun _ : {i : ι // i ∈ s} => μ)).prod
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf.mul_prod hg
  have hh := (hp.integrableOn_comp_preimage p.measurableEmbedding).2 hprod
  rw [hpre] at hh
  exact hh

theorem integral_lower_separated_product (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))
    (hbound : ∀ x ∈ binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i) ≤ F x) :
    (Fintype.card ι).choose s.card *
      ((∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
      (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
        ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hle := setIntegral_mono_on (integrableOn_binary_product μ A B s hf hg)
    (hF.mono_set (hinc s rfl)) (measurableSet_binaryRegion hA hB s) hbound
  rw [setIntegral_binary_product] at hle
  exact (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)).trans
    (integral_lower_binary_assignments μ hA hB hd s hF hF0 hsym hinc)

omit [MeasurableSpace X] [Fintype ι] [DecidableEq ι] in

theorem binomial_factorial_cancel {n k : ℕ} (hk : k ≤ n) {a b I : ℝ}
    (h : (n.choose k : ℝ) * (a * b) ≤ I) :
    (a / (k.factorial : ℝ)) * (b / ((n-k).factorial : ℝ)) ≤ I / (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (le_div_iff₀ hn).2
  rw [Nat.cast_choose ℝ hk] at h
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end Assignments

end ContinuumTemperature
end

end OAI
