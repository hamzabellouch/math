import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridAlignment
import OAI.Analysis.HardSphere.PathBounds.VisitCounts
import OAI.Analysis.HardSphere.Thermodynamics.ShiftCloseTail

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

lemma joint_event_image {W V U : Type*} [MeasurableSpace W] [DecidableEq U]
    (μ : Measure W) (f : V→U) (P : U→W→Prop) (A : Finset V) :
    μ {ω | ∀v∈A,P (f v) ω}=μ {ω | ∀u∈A.image f,P u ω} := by
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,Finset.mem_image,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]

lemma grid_visitors_eq {n K : ℕ} [NeZero K] (L : Length)
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) Set.univ (gridSite v) ω=(visitors (gridCenter L v) ω).card := by
  classical
  rw [grid_visitorCount]
  apply congrArg Finset.card
  ext i
  simp [visitors]

lemma grid_longVisitors_eq {n K : ℕ} [NeZero K] (L : Length)
    (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    ShiftVisits.visitorCount L (gridShift L) {p | 1 < intervalDiameter 0 1 p} (gridSite v) ω=
      (longVisitors (gridCenter L v) ω).card := by
  classical
  rw [grid_visitorCount]
  apply congrArg Finset.card
  ext i
  simp [longVisitors,and_comm]

lemma grid_nonregular_iff {n K : ℕ} [NeZero K] (L : Length)
    (m : ℕ) (r R C S : ℝ) (u : Time) (v : Fin 3→Fin K) (ω : ConfigurationPath n L) :
    (¬∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)) ↔
    1≤(ShiftVisits.visitorCount L (gridShift L) {p | ¬Regular m r R C u S p} (gridSite v) ω:ℝ) := by
  classical
  rw [grid_visitorCount]
  have hcast (k : ℕ) : (1:ℝ)≤(k:ℝ) ↔ 1≤k := by exact_mod_cast Iff.rfl
  rw [hcast,Finset.one_le_card]
  change (¬∀i, _ → _) ↔ ∃i, i∈_
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_ofPred_eq]
  push Not
  exact exists_congr (fun i ↦ and_comm)

lemma ofReal_power_tail {x q : ℝ} (hx : 0≤x) (hq : 0≤q) (h : x≤q^6) (n : ℕ) :
    ENNReal.ofReal (x^n)≤(ENNReal.ofReal q)^(6*n) := by
  rw [pow_mul,←ENNReal.ofReal_pow hq,←ENNReal.ofReal_pow (pow_nonneg hq _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hx h n)

lemma exp_power_tail {x q : ℝ} (hq : 0≤q) (h : Real.exp x≤q^6) (n : ℕ) :
    ENNReal.ofReal (Real.exp (x*(n:ℝ)))≤(ENNReal.ofReal q)^(6*n) := by
  rw [mul_comm x (n:ℝ),Real.exp_nat_mul]
  exact ofReal_power_tail (Real.exp_pos x).le hq h n

lemma grid_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (Fin 3→Fin K)),
      groundPathLaw n L (α/D) T g {ω | ∀ v∈A,
        θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω q)).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_translated_stationary_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,G,hb,hb1,hG,hl,ht⟩ := htail θ hθ
  refine ⟨b,G,hb,hb1,hG,hl,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hh⟩ := ht αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K inst L hL D α hL100 hDeq hD hα hαmax g hg T hT q A
  have h := hh n K L hL D α hL100 hDeq hD hα hαmax g hg T hT q (gridShift L) (A.image gridCube)
  rw [Finset.card_image_of_injective _ gridCube_injective] at h
  convert h using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,Finset.mem_image,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,shifted_unitCenter]

end HardSphere.Groups

end
end

end

end OAI
