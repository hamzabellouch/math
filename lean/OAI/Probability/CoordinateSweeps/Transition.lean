import Mathlib
import OAI.Probability.CoordinateSweeps.Kernel

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
namespace Grid.Holes
variable {G : Grid} {h : ℕ}

theorem log_size (G : Grid) : Real.log (G.size : ℝ) =
    ∑ j, Real.log ((2 ^ G.bits j : ℕ) : ℝ) := by
  rw [size,Nat.cast_prod,Real.log_prod]
  intro j _
  positivity

theorem log_probability_zero (H : G.Holes h) :
    Real.log (H.probability 0) = H.cost - (h : ℝ) * Real.log (G.size : ℝ) := by
  have hp (j : Fin G.b) (L : G.Line j) :
      (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (H.lineCount_le j L)).ne'
  have hline (j : Fin G.b) (L : G.Line j) :
      Real.log (((2 ^ G.bits j : ℕ) : ℝ)^H.lineCount j L /
        ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)) =
      (H.lineCount j L : ℝ) * Real.log ((2 ^ G.bits j : ℕ) : ℝ) -
        Real.log ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ) := by
    rw [Real.log_div (by positivity) (hp j L),Real.log_pow]
  have hs (j : Fin G.b) : ∑ L : G.Line j, (H.lineCount j L : ℝ) = h := by
    exact_mod_cast H.sum_lineCount j
  rw [H.probability_zero, Real.log_prod (by
    intro j _
    exact Finset.prod_ne_zero_iff.mpr (fun L _ => inv_ne_zero (hp j L)))]
  have hsum (j : Fin G.b) :
      Real.log (∏ L : G.Line j, (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)⁻¹)) =
        ∑ L : G.Line j, -Real.log ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ) := by
    rw [Real.log_prod (fun L _ => inv_ne_zero (hp j L))]
    simp only [Real.log_inv]
  simp_rw [hsum]
  unfold cost
  simp_rw [hline,Finset.sum_sub_distrib,← Finset.sum_mul,hs]
  simp only [Finset.sum_neg_distrib]
  rw [← Finset.mul_sum,log_size]
  ring

theorem probability_zero_pos (H : G.Holes h) : 0 < H.probability 0 := by
  rw [H.probability_zero]
  apply Finset.prod_pos
  intro j _
  apply Finset.prod_pos
  intro L _
  apply inv_pos.mpr
  exact_mod_cast Nat.descFactorial_pos.mpr (H.lineCount_le j L)

theorem probability_zero_eq_exp (H : G.Holes h) :
    H.probability 0 = Real.exp (H.cost - (h : ℝ)*Real.log (G.size : ℝ)) := by
  rw [← H.log_probability_zero,Real.exp_log H.probability_zero_pos]

/- Augmented holes retain the ordered first h trajectories exactly. -/
def Extends {t : ℕ} (J : G.Holes (h+t)) (H : G.Holes h) : Prop :=
  ∀ (i : Fin h) (j : Fin (G.b+1)), J.path (Fin.castAdd t i) j = H.path i j

def extraCount {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (Finset.univ.filter (fun i : Fin t => J.OnLine j L (Fin.natAdd h i))).card

theorem lineCount_add {t : ℕ} (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j) :
    J.lineCount j L = H.lineCount j L + J.extraCount j L := by
  unfold Extends at he
  unfold lineCount extraCount OnLine
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro i _
    simp only [he i j.castSucc]
  · intro i _
    split_ifs <;> rfl

theorem sum_extraCount {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) :
    ∑ L : G.Line j, J.extraCount j L = t := by
  unfold extraCount
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (i : Fin t) : (∑ L : G.Line j, if J.OnLine j L (Fin.natAdd h i) then 1 else 0) = 1 := by
    let L₀ : G.Line j := fun k => J.path (Fin.natAdd h i) j.castSucc k
    rw [Finset.sum_eq_single L₀]
    · exact ite_eq_left rfl
    · intro L _ hL
      apply ite_eq_right
      intro he
      exact hL he.symm
    · simp
  simp_rw [hh]
  simp

theorem no_extra_iff {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) :
    J.extraCount j L = 0 ↔ ∀ i : Fin t, ¬ J.OnLine j L (Fin.natAdd h i) := by
  simp [extraCount,Finset.card_eq_zero]

theorem lineCompatible_eq_of_no_extra {t : ℕ} (J : G.Holes (h+t))
    (H : G.Holes h) (he : J.Extends H) (j : Fin G.b) (L : G.Line j)
    (hno : J.extraCount j L = 0) (σ : Equiv.Perm (Cube (G.bits j))) :
    J.LineCompatible j L σ ↔ H.LineCompatible j L σ := by
  unfold Extends at he
  have hn := (J.no_extra_iff j L).mp hno
  constructor
  · intro hj i
    have hi : J.OnLine j L (Fin.castAdd t i.val) := by
      change (fun k : {k : Fin G.b // k ≠ j} => J.path (Fin.castAdd t i.val) j.castSucc k) = L
      simpa only [OnLine,he i.val j.castSucc] using i.property
    have hh := hj ⟨Fin.castAdd t i.val,hi⟩
    simpa only [he] using hh
  · intro hh i
    have hcases : (∃ k : Fin h, i.val = Fin.castAdd t k) ∨
        (∃ k : Fin t, i.val = Fin.natAdd h k) :=
      Fin.addCases (fun k : Fin h => Or.inl ⟨k,rfl⟩)
        (fun k : Fin t => Or.inr ⟨k,rfl⟩) i.val
    rcases hcases with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hi : H.OnLine j L k := by
        have hi := i.property
        rw [hk] at hi
        simpa only [OnLine,he] using hi
      have hv := hh ⟨k,hi⟩
      simpa only [hk,he] using hv
    · exact False.elim (hn k (hk ▸ i.property))

end Grid.Holes

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem assignments_pos_of_comparison {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (hlo : ∀ g, (1/2 : ℝ)*uniform (Equiv.Perm Ω) g ≤ μ g)
    (x y : Fin h ↪ Ω) : 0 < μ.assignments x y := by
  have hp := uniform_assignments_pos x y
  exact lt_of_lt_of_le (by positivity) (le_assignments μ (uniform _) (1/2) hlo x y)

theorem assignments_ratio_comparison {h h' : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (hlo : ∀ g, (1/2 : ℝ)*uniform (Equiv.Perm Ω) g ≤ μ g)
    (hhi : ∀ g, μ g ≤ 2*uniform (Equiv.Perm Ω) g)
    (x y : Fin h ↪ Ω) (x' y' : Fin h' ↪ Ω) :
    μ.assignments x' y' / μ.assignments x y ≤
      4 * ((uniform (Equiv.Perm Ω)).assignments x' y' /
        (uniform (Equiv.Perm Ω)).assignments x y) := by
  have hp := uniform_assignments_pos x y
  calc
    _ ≤ (2*(uniform (Equiv.Perm Ω)).assignments x' y') /
        ((1/2)*(uniform (Equiv.Perm Ω)).assignments x y) :=
      div_le_div₀ (mul_nonneg (by norm_num) ((uniform _).assignments_nonneg x' y'))
        (assignments_le μ (uniform _) 2 hhi x' y') (by positivity)
        (le_assignments μ (uniform _) (1/2) hlo x y)
    _ = _ := by ring
end FiniteLaw

namespace Grid.Holes
variable {G : Grid} {h t : ℕ}

def lineProb (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  μ.assignments (H.lineInput j L) (H.lineOutput j L)

theorem lineProb_nonneg (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : 0 ≤ H.lineProb j L μ :=
  μ.assignments_nonneg _ _

theorem uniform_lineProb_pos (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    0 < H.lineProb j L (FiniteLaw.uniform _) := FiniteLaw.uniform_assignments_pos _ _

theorem lineProb_eq_of_no_extra (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j) (hno : J.extraCount j L = 0)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    J.lineProb j L μ = H.lineProb j L μ := by
  unfold lineProb
  rw [← J.lineProbability_eq,← H.lineProbability_eq]
  let e : {σ // J.LineCompatible j L σ} ≃ {σ // H.LineCompatible j L σ} :=
    Equiv.subtypeEquivRight (J.lineCompatible_eq_of_no_extra H he j L hno)
  exact Equiv.sum_comp e (fun σ => μ σ.val)

def usedLine (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) : ℕ :=
  if J.extraCount j L = 0 then 0 else 1

theorem sum_usedLine_le (J : G.Holes (h+t)) :
    (∑ j, ∑ L : G.Line j, J.usedLine j L) ≤ t*G.b := by
  calc
    _ ≤ ∑ j, ∑ L : G.Line j, J.extraCount j L := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro L _
      unfold usedLine
      split_ifs <;> omega
    _ = t*G.b := by simp [J.sum_extraCount,Nat.mul_comm]

theorem lineProb_ratio_le (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hlo : ∀ g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ μ g)
    (hhi : ∀ g, μ g ≤ 2*FiniteLaw.uniform _ g) :
    J.lineProb j L μ / H.lineProb j L μ ≤
      (4 : ℝ) ^ J.usedLine j L *
        (J.lineProb j L (FiniteLaw.uniform _) / H.lineProb j L (FiniteLaw.uniform _)) := by
  by_cases hno : J.extraCount j L = 0
  · rw [J.lineProb_eq_of_no_extra H he j L hno μ,
      J.lineProb_eq_of_no_extra H he j L hno (FiniteLaw.uniform _)]
    have hp : 0 < H.lineProb j L μ := μ.assignments_pos_of_comparison hlo _ _
    have hu := H.uniform_lineProb_pos j L
    simp [usedLine,hno,hp.ne',hu.ne']
  · simpa only [lineProb,usedLine,ite_eq_right hno,pow_one] using
      μ.assignments_ratio_comparison hlo hhi (H.lineInput j L) (H.lineOutput j L)
        (J.lineInput j L) (J.lineOutput j L)

theorem probability_prod_lineProb (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L : G.Line j, H.lineProb j L (lineLaw (G.bits j) z hz hz') :=
  H.probability_eq_assignments hz hz'

theorem probability_zero_prod_lineProb (H : G.Holes h) :
    H.probability 0 = ∏ j, ∏ L : G.Line j, H.lineProb j L (FiniteLaw.uniform _) := by
  rw [H.probability_prod_lineProb (le_refl 0) zero_le_one]
  congr 1
  funext j
  congr 1
  funext L
  congr 1
  ext σ
  simp [lineLaw,FiniteLaw.mix]

/- Only a line visited by a new path may spend the factor four. Thus the
factor count is at most t*b, not the total number of stage-lines. -/
theorem probability_ratio_comparison (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    J.probability z / H.probability z ≤
      (4 : ℝ)^(t*G.b) * (J.probability 0 / H.probability 0) := by
  let μ (j : Fin G.b) := lineLaw (G.bits j) z hz hz'
  have heq : J.probability z / H.probability z =
      ∏ j, ∏ L : G.Line j, J.lineProb j L (μ j) / H.lineProb j L (μ j) := by
    rw [J.probability_prod_lineProb hz hz',H.probability_prod_lineProb hz hz',
      ← Finset.prod_div_distrib]
    simp_rw [← Finset.prod_div_distrib]
    rfl
  rw [heq]
  calc
    _ ≤ ∏ j, ∏ L : G.Line j, (4 : ℝ)^J.usedLine j L *
        (J.lineProb j L (FiniteLaw.uniform _) / H.lineProb j L (FiniteLaw.uniform _)) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Finset.prod_nonneg (fun L _ => div_nonneg (J.lineProb_nonneg j L _) (H.lineProb_nonneg j L _))
      · intro j _
        apply Finset.prod_le_prod₀
        · intro L _; exact div_nonneg (J.lineProb_nonneg j L _) (H.lineProb_nonneg j L _)
        · intro L _; exact J.lineProb_ratio_le H he j L (μ j) (hlo j) (hhi j)
    _ = (4 : ℝ)^(∑ j, ∑ L : G.Line j, J.usedLine j L) *
        (J.probability 0 / H.probability 0) := by
      simp_rw [Finset.prod_mul_distrib,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
      rw [← J.probability_zero_prod_lineProb,← H.probability_zero_prod_lineProb]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) J.sum_usedLine_le)
      (div_nonneg J.probability_zero_pos.le H.probability_zero_pos.le)

/- Source 03-paths (4), in the exactly equal exponential notation. The ratio
is the conditional probability of the complete augmented paths. -/
theorem conditional_transition_bound (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    J.probability z / H.probability z ≤
      Real.exp (-(t : ℝ)*Real.log (G.size : ℝ) + J.cost-H.cost + Real.log 4*(t : ℝ)*G.b) := by
  apply (J.probability_ratio_comparison H he hz hz' hlo hhi).trans_eq
  rw [J.probability_zero_eq_exp,H.probability_zero_eq_exp,← Real.exp_sub]
  have h4 : (4 : ℝ)^(t*G.b) = Real.exp (Real.log 4 * (t : ℝ)*G.b) := by
    rw [show Real.log 4 * (t : ℝ)*G.b = (t*G.b : ℕ)*Real.log 4 by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<4)]
  rw [h4,← Real.exp_add]
  congr 1
  push_cast
  ring
end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k t : ℕ}

/- An injection into the actual available input slots. -/
def ValidInput (H : G.Holes h) (x : Fin t → G.Slot) : Prop :=
  Function.Injective x ∧ ∀ i a, x i ≠ H.path a 0

/- A feasible endpoint event augments the prescribed holes by the uniquely
determined auxiliary paths. The witness is used only to verify disjointness. -/
def augment (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i) :
    G.Holes (h+t) where
  path i s := Fin.append (fun a => H.path a s) (fun a => G.pathBetween (u a) (v a) s) i
  disjoint s := by
    apply Fin.append_injective_iff.mpr
    refine ⟨H.disjoint s, ?_, ?_⟩
    · intro a b he
      have ha := G.boundary_eq_pathBetween ω (u a) s
      have hb := G.boundary_eq_pathBetween ω (u b) s
      rw [hv a] at ha
      rw [hv b] at hb
      exact hu.1 ((G.boundary ω s).injective (ha.trans (he.trans hb.symm)))
    · intro a b he
      have hb := G.boundary_eq_pathBetween ω (u b) s
      rw [hv b] at hb
      exact hu.2 b a ((G.boundary ω s).injective ((hω a s).trans (he.trans hb.symm))).symm
  coordinate_step i j l hlj := by
    cases i using Fin.addCases with
    | left a => simpa using H.coordinate_step a j l hlj
    | right a => simpa using G.pathBetween_step (u a) (v a) j l hlj

@[simp] theorem augment_old (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (i : Fin h) (s : Fin (G.b+1)) :
    (H.augment u v hu ω hω hv).path (Fin.castAdd t i) s = H.path i s := by
  simp [augment]

@[simp] theorem augment_new (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (i : Fin t) (s : Fin (G.b+1)) :
    (H.augment u v hu ω hω hv).path (Fin.natAdd h i) s =
      G.pathBetween (u i) (v i) s := by
  simp [augment]

theorem augment_extends (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i) :
    (H.augment u v hu ω hω hv).Extends H := by
  intro i s; simp

/- Exact equivalence of conditioning events, including all stage boundaries. -/
theorem augment_compatible_iff (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i)
    (ν : G.Choices) :
    (H.augment u v hu ω hω hv).Compatible ν ↔
      H.Compatible ν ∧ ∀ i, G.sweep ν (u i) = v i := by
  constructor
  · intro hJ
    constructor
    · intro a s
      have hh := hJ (Fin.castAdd t a) s
      simpa only [augment_old] using hh
    · intro a
      have hh := hJ (Fin.natAdd h a) (Fin.last G.b)
      simpa only [augment_new, Grid.pathBetween_zero, Grid.pathBetween_last, Grid.sweep, Fin.val_last] using hh
  · rintro ⟨hν,he⟩
    intro i s
    cases i using Fin.addCases with
    | left a => simpa only [augment_old] using hν a s
    | right a =>
      simp only [augment_new, Grid.pathBetween_zero]
      rw [G.boundary_eq_pathBetween, he a]

/- A canonical enumeration of a selected list of auxiliary cards. -/
def selected (A : Finset (Fin k)) : Fin A.card ↪ Fin k :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem selected_mem (A : Finset (Fin k)) (i : Fin A.card) : selected A i ∈ A :=
  ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm i).property

theorem selected_range (A : Finset (Fin k)) (a : Fin k) (ha : a ∈ A) :
    ∃ i, selected A i = a := by
  let i := (Fintype.equivFinOfCardEq (Fintype.card_coe A)) ⟨a,ha⟩
  exact ⟨i, congrArg Subtype.val ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm_apply_apply _)⟩

theorem validInput_selected (H : G.Holes h) (u : Fin k → G.Slot) (hu : H.ValidInput u)
    (A : Finset (Fin k)) : H.ValidInput (fun i => u (selected A i)) := by
  exact ⟨hu.1.comp (selected A).injective, fun i a => hu.2 _ a⟩

theorem endpointEvent_iff_selected (u v : Fin k → G.Slot) (A : Finset (Fin k))
    (ω : G.Choices) : G.endpointEvent u v A ω ↔
      ∀ i : Fin A.card, G.sweep ω (u (selected A i)) = v (selected A i) := by
  constructor
  · intro he i
    exact he _ (selected_mem A i)
  · intro he a ha
    obtain ⟨i,rfl⟩ := selected_range A a ha
    exact he i

end CoordinateSweeps.Grid.Holes

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/

end
end
open scoped Matrix.Norms.L2Operator

end OAI
