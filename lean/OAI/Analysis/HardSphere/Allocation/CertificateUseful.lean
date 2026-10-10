import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalTrialTail
import OAI.Analysis.HardSphere.Allocation.CertificateTrialGeometry
import OAI.Analysis.HardSphere.Bridges.Geometry

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem certificate_useful_list {ell b Alo A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hAlo : 0 < Alo) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D α : ℝ,D₀ ≤ D → Alo ≤ α → α ≤ A →
    ∀(N K m n : ℕ) [Nontrivial (Fin N)] (L : Length),50 < L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀(w : Time),t*(w:ℝ)=D⁻¹ →
    ∀(θ : ℝ),θ ≤ ell/6 →
    ∀(v : Fin 3→Fin K) (c : Point),projectPoint L c=gridCenter L v →
    ∀(ω : ConfigurationPath N L),
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    ∀(label : Fin m→Fin N),Function.Injective label →
    Finset.univ.image label=eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω →
    ∀(B : Fin 7→Set Point),(∀j,MeasurableSet (B j)) → (∀j,volume (B j)=1) →
      (∀j u,u∈B j → ‖u-c‖ ≤ 3) →
    ∃y z : Fin m→Point,
      (∀i,projectPoint L (y i)=ω 0 (label i)) ∧
      (∀i,projectPoint L (z i)=ω 1 (label i)) ∧
      ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
        (b*D^(-(1/3):ℝ)/8) w (y i) (z i) c (fun j ↦ onePathAt j ω) (label i) B)).card:ℝ) ≤ (m:ℝ)/10 := by
  obtain ⟨cG,MG,hcG,hMG,htail⟩ := wiener_norm_gaussian_tail
  have htail' (R : ℝ) (hR : 0 ≤ R) :
      wiener {β | R ≤ ‖β‖} ≤ ENNReal.ofReal MG.toReal*ENNReal.ofReal (Real.exp (-cG*R^2)) := by
    rw [ENNReal.ofReal_toReal hMG.ne]
    exact htail R hR
  obtain ⟨t₀,ht₀,hs⟩ := physical_useful_list hell hb hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₁,hD₁,hs⟩ := hs t ht htt (t/Alo^2+1) MG.toReal cG (t/A^2)
    ENNReal.toReal_nonneg hcG (by positivity) htail'
  obtain ⟨D₂,hgeom⟩ := eventually_atTop.1 (source_trial_geometry hA hb ht)
  refine ⟨max D₁ D₂,hD₁.trans (le_max_left _ _),?_⟩
  intro D α hDD hαlo hαA N K m n _ L hL hn w hw θ hθ v c hc ω cert label hinj himage B hB hBvol hBv
  subst n
  have h1 : D₁ ≤ D := (le_max_left _ _).trans hDD
  have h2 : D₂ ≤ D := (le_max_right _ _).trans hDD
  have hα := hAlo.trans_le hαlo
  rcases hgeom D h2 α hα hαA with
    ⟨hD,hn,hr1,hsmall,hτ,hnscale,hw0,hw1,hwindow,hlarge,hdrift,hdrift',hwin,hrelax,hiso⟩
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < α/D := by positivity
  have hDa : D*(α/D)=α := by field_simp
  have hbnd := sourceHalf_bounds ht hr hD hAlo
    (show Alo ≤ D*(α/D) by rw [hDa]; exact hαlo)
    (show D*(α/D) ≤ A by rw [hDa]; exact hαA)
  obtain ⟨hm,hmH,hel⟩ := eligible_list_size _ _ _ _ _ _ ell θ H D hDp.le hθ _ v ω cert label hinj himage
  obtain ⟨y,z,hyp,hzp,hy,hz,hsepY,hsepZ,hj,hreg,hisoY,hisoZ,hfar⟩ :=
    certificate_trial_geometry hL _ _ _ _ _ _ ell θ H D (by positivity) _ v c hc ω cert label hinj hel hiso
  have hwd : (w:ℝ)=D⁻¹/t := (eq_div_iff ht.ne').mpr (by nlinarith [hw])
  refine ⟨y,z,hyp,hzp,?_⟩
  exact hs D α h1 hα hαA L N m _ hn hL hm hmH y z c (fun j ↦ onePathAt j ω) label
    (visitors (gridCenter L v) ω) w B hj hbnd.1 hbnd.2 hr1 hsmall hτ hnscale hw
    hwindow hlarge hdrift hdrift' (by rw [hwd]; exact hwin) hrelax hy hz hsepY hsepZ
    hreg hisoY hisoZ hfar hB hBvol hBv

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

lemma allocated_restriction_half_bad (E B : Finset I) (total q : ℕ)
    (hE : total≤E.card) (group : Fin (2*q)↪Fin total)
    (hB : 10*(E∩B).card≤E.card) :
    (allocationPMF E total).toMeasure
      {a | ∃f,a=some f ∧ q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^q) := by
  have hq : 2*q≤E.card := (show 2*q≤total by simpa using Fintype.card_le_of_embedding group).trans hE
  have h := allocation_half_bad E B q hq hB
  have hu := congrArg PMF.toMeasure (allocated_group_uniform E total (2*q) hE group)
  rw [←PMF.toMeasure_map _ _ (measurable_of_countable _)] at hu
  rw [←hu,Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete)] at h
  convert h using 2
  ext a
  cases a with
  | none => simp
  | some f => simp

omit [Fintype I] in
lemma enumerated_bad_card {m : ℕ} (label : Fin m→I) (hinj : Function.Injective label)
    (P : Fin m→Prop) :
    ((Finset.univ.image label)∩((Finset.univ.filter (fun i ↦ ¬P i)).image label)).card=
      (Finset.univ.filter (fun i ↦ ¬P i)).card := by
  rw [Finset.inter_eq_right.mpr (Finset.image_subset_image (Finset.filter_subset _ _)),
    Finset.card_image_of_injective _ hinj]

lemma enumerated_failure_probability {m : ℕ} (label : Fin m→I) (hinj : Function.Injective label)
    (P : Fin m→Prop) (hP : ((Finset.univ.filter (fun i ↦ ¬P i)).card:ℝ)≤(m:ℝ)/10)
    (total q : ℕ) (htotal : total ≤ m) (group : Fin (2*q)↪Fin total) :
    (allocationPMF (Finset.univ.image label) total).toMeasure
      {a | ∃f,a=some f ∧ q ≤ (Finset.univ.filter
        (fun k ↦ f (group k)∈(Finset.univ.filter (fun i ↦ ¬P i)).image label)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^q) := by
  have hcard : (Finset.univ.image label).card=m := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  apply allocated_restriction_half_bad _ _ total q (by simpa [hcard] using htotal) group
  rw [enumerated_bad_card label hinj P,hcard]
  have h : (10:ℝ)*((Finset.univ.filter (fun i ↦ ¬P i)).card:ℝ)≤(m:ℝ) := by linarith
  exact_mod_cast h

end HardSphere.Sampling

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem certificate_useful_groups {ell b Alo A H : ℝ}
    (hell : 0 < ell) (hb : 0 < b) (hAlo : 0 < Alo) (hA : 0 < A) (hH : 0 < H) :
    ∃t₀ : ℝ,0 < t₀ ∧ ∀t : ℝ,0 < t → t ≤ t₀ →
    ∃D₀ : ℝ,1 ≤ D₀ ∧ ∀D α : ℝ,D₀ ≤ D → Alo ≤ α → α ≤ A →
    ∀(N K m n : ℕ) [Nontrivial (Fin N)] (L : Length),50 < L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀(w : Time),t*(w:ℝ)=D⁻¹ →
    ∀(θ : ℝ),θ ≤ ell/6 →
    ∀(v : Fin 3→Fin K) (c : Point),projectPoint L c=gridCenter L v →
    ∀(ω : ConfigurationPath N L),
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    ∀(label : Fin m→Fin N),Function.Injective label →
    Finset.univ.image label=eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω →
    ∀(B : Fin 7→Set Point),(∀j,MeasurableSet (B j)) → (∀j,volume (B j)=1) →
      (∀j u,u∈B j → ‖u-c‖ ≤ 3) →
    ∃y z : Fin m→Point,
      (∀i,projectPoint L (y i)=ω 0 (label i)) ∧
      (∀i,projectPoint L (z i)=ω 1 (label i)) ∧
      ((Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
        (b*D^(-(1/3):ℝ)/8) w (y i) (z i) c (fun j ↦ onePathAt j ω) (label i) B)).card:ℝ) ≤ (m:ℝ)/10 ∧
      ∀total q : ℕ,total ≤ m → ∀group : Fin (2*q)↪Fin total,
      (Sampling.allocationPMF
        (eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
          (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω) total).toMeasure
        {a | ∃f,a=some f ∧ q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈
          (Finset.univ.filter (fun i ↦ ¬StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
        (b*D^(-(1/3):ℝ)/8) w (y i) (z i) c (fun j ↦ onePathAt j ω) (label i) B)).image label)).card}≤
        ENNReal.ofReal ((2/5:ℝ)^q) := by
  obtain ⟨t₀,ht₀,hs⟩ := certificate_useful_list hell hb hAlo hA hH
  refine ⟨t₀,ht₀,?_⟩
  intro t ht htt
  obtain ⟨D₀,hD₀,hs⟩ := hs t ht htt
  refine ⟨D₀,hD₀,?_⟩
  intro D α hDD hαlo hαA N K m n _ L hL hn w hw θ hθ v c hc ω cert label hinj himage B hB hBvol hBc
  obtain ⟨y,z,hyp,hzp,huse⟩ := hs D α hDD hαlo hαA N K m n L hL hn w hw θ hθ v c hc ω cert label hinj himage B hB hBvol hBc
  refine ⟨y,z,hyp,hzp,huse,?_⟩
  intro total q htotal group
  have h := Sampling.enumerated_failure_probability label hinj
    (fun i ↦ StrongExcept n t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
        (b*D^(-(1/3):ℝ)/8) w (y i) (z i) c (fun j ↦ onePathAt j ω) (label i) B) huse total q htotal group
  simpa only [himage] using h

end HardSphere.Groups

end
end

end

end OAI
