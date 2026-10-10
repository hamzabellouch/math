import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalCodedMoment

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma padded_label_encounter (p q : SimplePath x y) (s : DiscreteTorus K→Finset J)
    (home : J→DiscreteTorus K)
    (hn : ∀v∈departureSites p∪departureSites q,(s v).Nonempty)
    (hh : ∀v∈departureSites p∪departureSites q,∀j∈s v,home j=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*((s v).card:ℝ)) (R : ℕ) :
    (∫⁻z,∫⁻w,(ENNReal.ofReal G)^(1+(fieldLabelImage p z∩fieldLabelImage q w).card)
      ∂Measure.pi (fun v ↦ uniformLabels (s v)) ∂Measure.pi (fun v ↦ uniformLabels (s v)))≤
      ENNReal.ofReal (G*Real.exp ((2*(G-1)/M)*(simpleEncounter R p q:ℝ))) := by
  have G0 : 0≤G := by linarith
  rw [←lintegral_prod (fun z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J) ↦
    (ENNReal.ofReal G)^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card))
    (measurable_of_countable _).aemeasurable]
  simp_rw [←ENNReal.ofReal_pow G0]
  rw [←ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (ae_of_all _ (fun _ ↦ pow_nonneg G0 _))]
  apply ENNReal.ofReal_le_ofReal
  apply (padded_label_overlap p q s home hn hh G M hG hM hm).trans
  apply mul_le_mul_of_nonneg_left _ G0
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast shared_departures_le_encounters R p q
  · positivity

lemma encounter_absorb (G M κ δ : ℝ) (hG : 1≤G) (_hM : 0<M) (hδ : 0<δ)
    (hκ : 2*(G-1)/M-8*Real.log δ≤κ) (n : ℕ) :
    ENNReal.ofReal (G*Real.exp ((2*(G-1)/M)*(n:ℝ))) *
        (ENNReal.ofReal δ)⁻¹^(8*n) ≤ ENNReal.ofReal (G*Real.exp (κ*(n:ℝ))) := by
  have G0 : 0≤G := by linarith
  have he : (δ⁻¹)^(8*n)=Real.exp ((-8*Real.log δ)*(n:ℝ)) := by
    have H := Real.exp_nat_mul (-Real.log δ) (8*n)
    rw [Real.exp_neg,Real.exp_log hδ] at H
    exact H.symm.trans (congrArg Real.exp (by push_cast; ring))
  rw [←ENNReal.ofReal_inv_of_pos hδ,←ENNReal.ofReal_pow (inv_nonneg.mpr hδ.le),
    ←ENNReal.ofReal_mul (mul_nonneg G0 (Real.exp_nonneg _)),he]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ G0
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physicalLabel_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p p' : SimplePath x y) (hM : 0<M)
    (hsupply : ∀v∈departureSites p∪departureSites p',
      (M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q : ℝ≥0∞) (δ B κ : ℝ) (hδ : 0<δ) (hB : 1≤B) (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻z,∫⁻z',∫⁻w,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d)≤
      ENNReal.ofReal (B*Real.exp (κ*(simpleEncounter 30 p p':ℝ))) := by
  let s := fun v ↦ branchAccessible hL g m t r R C S u particle v d
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hn : ∀v∈departureSites p∪departureSites p',(s v).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    have H := hsupply v hv
    have : (0:ℝ)<(s v).card := by dsimp [s]; linarith
    exact_mod_cast this
  have hhome : ∀v∈departureSites p∪departureSites p',∀j∈s v,
      indexSite (datumHome hL d (particle j))=v := by
    intro v _ j hj
    rw [(branchAccessible_home hL g m t r R C S u particle v d j hj).1]
    exact indexSite_siteIndex v
  have ha : ∀i : Fin p.val.length,(s (pathVertexEmbedding p i.castSucc)).Nonempty := by
    intro i
    exact hn _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have ha' : ∀i : Fin p'.val.length,(s (pathVertexEmbedding p' i.castSucc)).Nonempty := by
    intro i
    exact hn _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have Hav := padded_label_encounter p p' s (fun j ↦ indexSite (datumHome hL d (particle j)))
    hn hhome B M hB hM' (fun v hv ↦ hsupply v (Finset.mem_union_left _ (Finset.mem_inter.mp hv).1)) 30
  have hlabels : physicalLabels hL g m t r R C S u particle d=Measure.pi (fun v ↦ uniformLabels (s v)) := by
    rw [physicalLabels, finiteKernelPi_apply]
    rfl
  calc
    _ ≤ ∫⁻z,∫⁻z',(ENNReal.ofReal B)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)*
      (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p')
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d := by
      apply lintegral_mono_ae
      filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
      apply lintegral_mono_ae
      filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z' hz'
      apply (physicalCoded_moment hL g m t r R C S ht hr u particle d hxy p p' z z' hz hz'
        ha ha' hm hp q (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) hq hsmall b).trans
      exact mul_le_mul' (pow_le_pow_left' hBt _) le_rfl
    _ = (∫⁻z,∫⁻z',(ENNReal.ofReal B)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)
        ∂physicalLabels hL g m t r R C S u particle d
        ∂physicalLabels hL g m t r R C S u particle d) *
        (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p') := by
      simp_rw [lintegral_mul_const _ (measurable_of_countable _)]
    _ ≤ ENNReal.ofReal (B*Real.exp ((2*(B-1)/M)*(simpleEncounter 30 p p':ℝ))) *
        (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p') := by
      apply mul_le_mul' _ le_rfl
      rwa [hlabels]
    _ ≤ _ := encounter_absorb B M κ δ hB hM' hδ hκ _

end HardSphere.Groups
end
end

end OAI
