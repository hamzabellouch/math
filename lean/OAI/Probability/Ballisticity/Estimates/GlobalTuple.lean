import Mathlib
import OAI.Probability.Ballisticity.Estimates.BudgetMeasurable
import OAI.Probability.Ballisticity.Estimates.GlobalProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalEndpointProfile_support {d : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : ∀ᵐ y ∂globalEndpointProfile e H ω,
      dot (realPosition y) (realPosition (step e))=(H:ℝ) := by
  apply normalizeOr_ae
  · apply (coordinate_hitKernel_supported e (0:Lattice d) H ω).mono
    intro y hy
    rw [signedHeight_projection,hy]
    simp [signedHeight]
  · rw [ae_dirac_iff (Set.to_countable _).measurableSet]
    rw [signedHeight_projection]
    have hh := signedHeight_add_nsmul_step e (0:Lattice d) H
    have hh : signedHeight e (H • step e) = H := by simpa [signedHeight] using hh
    exact_mod_cast hh

noncomputable def globalTupleProfile {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) : LayerTupleProfile (k:=k) e H := by
  let μ := Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)
  refine ⟨μ,inferInstance,?_⟩
  apply ae_all_iff.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin k => globalEndpointProfile e H ω)
    (i:=j)).eventually (globalEndpointProfile_support e H ω)

lemma globalTupleProfile_mass {d k : ℕ} (e : Direction d) (H : ℕ)
    (ω : Environment d) :
    (crossingQuenched (realPosition (step e)) 0 H ω)^k •
      (globalTupleProfile (k:=k) e H ω).val =
      rawTupleEndpointLaw (realPosition (step e)) H ω (fun _ : Fin k => 0) := by
  apply Measure.ext_of_singleton
  intro x
  have hm (j : Fin k) := congrArg (fun μ : Measure (Lattice d) => μ {x j})
    (globalEndpointProfile_mass e H ω)
  simp only [Measure.smul_apply,smul_eq_mul] at hm ⊢
  change _ * (Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)) {x} = _
  rw [Measure.pi_singleton,rawTupleEndpointLaw_singleton]
  simp_rw [←hm]
  rw [Finset.prod_mul_distrib]
  simp

lemma globalTupleProfile_measurable_below {d k : ℕ} (e : Direction d) (H : ℕ) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) H)) _
      (globalTupleProfile (k:=k) e H) := by
  let : MeasurableSpace (Environment d) := rowSigma (BelowHeight (realPosition (step e)) H)
  apply Measurable.subtype_mk
  apply TupleKernel.measurable_countable_measure
  intro x
  change Measurable (fun ω => (Measure.pi (fun _ : Fin k => globalEndpointProfile e H ω)) {x})
  simp_rw [Measure.pi_singleton]
  exact Finset.measurable_prod _ fun j _ =>
    (Measure.measurable_coe (measurableSet_singleton _)).comp (globalEndpointProfile_measurable_below e H)

end DirectionalTransience

end

section

open scoped BigOperators Classical
namespace DirectionalTransience

lemma injection_candidate_unique (x y R M : ℝ) (hR : 0 ≤ R) (hM : 2*R < M)
    (a b : ℕ) (ha : |x+M*(a+1)-y| < R) (hb : |x+M*(b+1)-y| < R) : a=b := by
  by_contra hab
  have hd : (1:ℝ) ≤ |(a:ℝ)-b| := by
    have hh0 : (0:ℤ) < |(a:ℤ)-b| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hab))
    have hh : (1:ℤ) ≤ |(a:ℤ)-b| := by omega
    exact_mod_cast hh
  have hn : |M*((a:ℝ)-b)| < 2*R := by
    calc
      _ = |(x+M*(a+1)-y)-(x+M*(b+1)-y)| := by congr 1; ring
      _ ≤ |x+M*(a+1)-y|+|x+M*(b+1)-y| := abs_sub _ _
      _ < 2*R := by linarith
  rw [abs_mul,abs_of_pos (lt_of_le_of_lt (by positivity) hM)] at hn
  nlinarith

lemma finite_injection_choice (k : ℕ) (R M : ℝ) (hR : 0 ≤ R) (hM : 2*R < M)
    (x : Fin k → ℝ) : ∃ m : Fin k → Fin k,
      ∀ i j, i ≠ j → R ≤ |(x i+M*((m i:ℕ)+1))-(x j+M*((m j:ℕ)+1))| := by
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨m,hm⟩ := ih (fun i => x i.castSucc)
    let bad : Fin k → Finset (Fin (k+1)) := fun j => Finset.univ.filter fun l =>
      |x (Fin.last k)+M*((l:ℕ)+1)-(x j.castSucc+M*((m j:ℕ)+1))| < R
    have hbad (j : Fin k) : (bad j).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      apply Fin.ext
      exact injection_candidate_unique _ _ R M hR hM _ _
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    let B := Finset.univ.biUnion bad
    have hB : B.card ≤ k := by
      calc
        B.card ≤ ∑ j, (bad j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum (fun j _ => hbad j)
        _ = k := by simp
    have hex : ∃ l : Fin (k+1), l ∉ B := by
      by_contra no
      have hu : B=Finset.univ := Finset.eq_univ_of_forall fun l => by simpa using not_exists.mp no l
      rw [hu] at hB
      simp only [Finset.card_univ,Fintype.card_fin] at hB
      omega
    obtain ⟨l,hl⟩ := hex
    have hlm (j : Fin k) : R ≤ |x (Fin.last k)+M*((l:ℕ)+1)-(x j.castSucc+M*((m j:ℕ)+1))| := by
      apply le_of_not_gt
      intro hh
      exact hl (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩)
    refine ⟨Fin.lastCases l (fun j => (m j).castSucc),?_⟩
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => simpa using hlm j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa only [Fin.lastCases_last,Fin.lastCases_castSucc,Fin.val_castSucc,abs_sub_comm] using hlm i
      | cast j =>
        simpa using hm i j (fun h => hij (congrArg Fin.castSucc h))

end DirectionalTransience

end

end OAI
