import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates
import OAI.Analysis.VlasovMaxwell.Population.BulkWeightCost
import OAI.Analysis.VlasovMaxwell.Retarded.DirectLorentzUniform

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma bounded_supported_test_mass {a b T : ℝ} {ψ : ℝ→ℝ}
    (hab : a≤b) (hψ : Continuous ψ) (hψ1 : ∀t,|ψ t|≤1)
    (hout : ∀t∉Icc a b,ψ t=0) : (∫t in Ioo (0:ℝ) T,|ψ t|)≤b-a := by
  have hs : tsupport ψ⊆Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    exact ht (hout t hn)
  have hc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hs
  have hi : Integrable ψ := hψ.integrable_of_hasCompactSupport hc
  have hone : Integrable ((Icc a b).indicator (fun _ : ℝ=>(1:ℝ))) :=
    (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  calc
    _≤∫t : ℝ,|ψ t| := setIntegral_le_integral hi.norm (ae_of_all _ (fun t=>abs_nonneg _))
    _≤∫t : ℝ,(Icc a b).indicator (fun _ : ℝ=>(1:ℝ)) t := by
      apply integral_mono hi.norm hone
      intro t
      by_cases ht : t∈Icc a b
      · rw [indicator_of_mem ht]; exact hψ1 t
      · simp [indicator_of_notMem ht,hout t ht]
    _=b-a := by rw [integral_indicator measurableSet_Icc, integral_const]; simp [hab]

lemma directionWeight_test {a b ℓ η I T : ℝ} (hη : 0<η) (hI : 0<I) (hℓ : η*I≤ℓ)
    (hlen : 2*ℓ≤b-a) (hb : b≤T) :
    (∀t,|directionWeight a b ℓ t|≤1) ∧
    (∀t∉Icc a b,directionWeight a b ℓ t=0) ∧
    (∀t∈Icc a b,|deriv (directionWeight a b ℓ) t|≤(2/η)/I) ∧
    (∀t∉Icc a b,deriv (directionWeight a b ℓ) t=0) ∧
    directionWeight a b ℓ T=0 := by
  have hl : 0<ℓ := (mul_pos hη hI).trans_le hℓ
  refine ⟨fun t=>by rw [abs_of_nonneg (directionWeight_bounds hl hlen).1]; exact (directionWeight_bounds hl hlen).2,
    fun t ht=>image_eq_zero_of_notMem_tsupport (fun hh=>ht (directionWeight_tsupport hl hlen hh)),?_,
    fun t ht=>directionWeight_deriv_outside hl hlen ht,?_⟩
  · intro t ht
    have hd := norm_deriv_le_of_lipschitz (x₀:=t) (directionWeight_lipschitz a b ℓ)
    simp only [Real.norm_eq_abs,NNReal.coe_add,coe_nnnorm,abs_of_pos (inv_pos.mpr hl)] at hd
    calc
      _≤ℓ⁻¹+ℓ⁻¹ := hd
      _=2/ℓ := by ring
      _≤2/(η*I) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hη hI) hℓ
      _=(2/η)/I := by ring
  · by_cases ht : T=b
    · rw [ht]; exact (directionWeight_endpoints hl hlen).2
    · exact image_eq_zero_of_notMem_tsupport (fun hh=>ht (le_antisymm (directionWeight_tsupport hl hlen hh).2 hb))

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ofReal_norm_three_add (u v w : Vec) :
    ENNReal.ofReal ‖u+v+w‖≤ENNReal.ofReal ‖u‖+ENNReal.ofReal ‖v‖+ENNReal.ofReal ‖w‖ := by
  rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ←ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))

lemma Admissible.selected_force_residual_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal ((4*Real.pi)⁻¹) *
        (ENNReal.ofReal ‖∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T
          (bulkSelection P M A w I) ψ p‖+
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) := by
  obtain ⟨Cb,hCb,hcost⟩ := hd.bulk_signed_cost_uniform T₀ D hD
  obtain ⟨Ci,hCi,hinit⟩ := selectedInitialKernel_integrable_bound hd.1.continuous hd.2.1 hd.2.2.1
  let C := Ci*(max 0 T₀)+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hcost M A hM hA] with P hco
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let Q := bulkSelection P M A w I
  let Id : ℝ→Vec→L[ℝ]Vec := fun _=>ContinuousLinearMap.id ℝ Vec
  have hB : 0≤B := by dsimp [B]; positivity
  have hIB : I≤B := by
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    calc
      I≤Real.sqrt I := hi
      _≤P*Real.sqrt I := le_mul_of_one_le_left (Real.sqrt_nonneg I) hP
      _≤B := le_add_of_nonneg_right (by positivity)
  have hc := hco hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ.continuous.measurable hψ1 hout hψd hdout
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hi := (hinit s.E s.B T F zX Q ψ Id 1 hT zero_le_one hψ.continuous.continuousOn
    continuous_const.continuousOn (fun _ _=>ContinuousLinearMap.norm_id_le)).2
  rw [mul_one] at hi
  have hmass := (bounded_supported_test_mass hab hψ.continuous hψ1 hout (T:=T)).trans hJI
  have hi' : ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ Id z‖≤Ci*(max 0 T₀)*B := by
    rw [hdata]
    apply hi.trans
    apply (mul_le_mul_of_nonneg_left hmass (mul_nonneg hCi hT)).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hTT.trans (le_max_right _ _)) hCi
    · exact hIB
    · exact hI.le
    · positivity
  have he := hs.selected_multiplier_decomposition hT F zX Q hψ (fun t _=>hψ1 t) hψT
    (W:=Id) (W':=fun _=>0) continuous_const continuous_const (fun t _=>hasDerivAt_const t _)
  simp only [Id,ContinuousLinearMap.id_apply] at he
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)),
    ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  apply mul_le_mul' le_rfl
  have hn := ofReal_norm_three_add
    (∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T Q ψ p)
    (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ Id z)
    (∫p : ℝ×Phase,selectedMultiplierCosts s F.flow zX T Q ψ Id (fun _=>0) p)
  apply (hn.trans (add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hi')) hc)).trans
  have heq : ENNReal.ofReal (Ci*(max 0 T₀)*B)+ENNReal.ofReal (Cb*B)=ENNReal.ofReal (C*B) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [C]
    ring
  change _≤ENNReal.ofReal ‖∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T Q ψ p‖+
    ENNReal.ofReal (C*B)+ENNReal.ofReal (C*w^(-1/2:ℝ))*K
  rw [add_assoc,←add_assoc (ENNReal.ofReal (Ci*(max 0 T₀)*B)),heq,←add_assoc]
  apply add_le_add le_rfl
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [mul_nonneg hCi (le_max_left (0:ℝ) T₀)])
    (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

end OAI
