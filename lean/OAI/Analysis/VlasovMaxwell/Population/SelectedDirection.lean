import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.SelectedRemainderPhysical

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal

namespace RVM

private lemma SmoothClassicalPrefix.selectedDirectionEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma sum_lintegral_le_lintegral_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    (∑i∈S,∫⁻x,f i x ∂μ) ≤ ∫⁻x,∑i∈S,f i x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

lemma directionWeight_family_label_kernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
    (τ : Ω→ℝ) (f : Ω→ℝ≥0∞) :
    (∑i∈S,∫⁻p,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) (τ p)| * f p ∂μ) ≤
      ∫⁻p,{p : Ω | τ p∈J}.indicator f p ∂μ := by
  classical
  apply (sum_lintegral_le_lintegral_sum μ S _).trans
  apply lintegral_mono
  intro p
  dsimp only
  by_cases hp : τ p∈J
  · rw [indicator_of_mem (show p ∈ {p : Ω | τ p∈J} from hp), ←Finset.sum_mul]
    exact (mul_le_mul' (directionWeight_sum_ofReal_le_one S a b ℓ hℓ hlen hdis (τ p))
      le_rfl).trans_eq (one_mul _)
  · rw [indicator_of_notMem (show p ∉ {p : Ω | τ p∈J} from hp)]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    have hz : directionWeight (a i) (b i) (ℓ i) (τ p)=0 :=
      image_eq_zero_of_notMem_tsupport (fun ht=>hp (hcell i hi
        (directionWeight_tsupport (hℓ i hi) (hlen i hi) ht)))
    rw [hz,abs_zero,ENNReal.ofReal_zero,zero_mul]

def selectedMultiplierBulkDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (W : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p) (actualLabelCutoffCost s α zX T Q p)‖ +
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
    (labelSelectedCutoff α zX T Q p • actualLabelRemainder s α zX T p)‖

def selectedMultiplierWeightDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
    (labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p)‖

def selectedMultiplierMovingDensity (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : ℝ≥0∞ :=
  ENNReal.ofReal ‖W' (labelReceiverTime α zX T p)
    (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p)‖

lemma selectedMultiplierCosts_norm_le (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W W' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    ENNReal.ofReal ‖selectedMultiplierCosts s α zX T Q ψ W W' p‖ ≤
      selectedMultiplierWeightDensity s α zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime α zX T p)| *
        selectedMultiplierBulkDensity s α zX T Q W p +
      selectedMultiplierMovingDensity s α zX T Q ψ W' p := by
  let τ := labelReceiverTime α zX T p
  have he : selectedMultiplierCosts s α zX T Q ψ W W' p =
      W τ (labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p) +
      (ψ τ • W τ (actualLabelCutoffCost s α zX T Q p) +
       ψ τ • W τ (labelSelectedCutoff α zX T Q p • actualLabelRemainder s α zX T p)) +
      W' τ (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p) := by
    simp only [selectedMultiplierCosts,selectedLabelCosts,map_add,map_smul,
      labelWeight,mul_smul,add_assoc,τ]
  rw [he]
  have hn (x y : Vec) : ENNReal.ofReal ‖x+y‖ ≤ ENNReal.ofReal ‖x‖+ENNReal.ofReal ‖y‖ := by
    rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  dsimp only [selectedMultiplierWeightDensity,selectedMultiplierMovingDensity]
  apply (hn _ _).trans
  apply add_le_add _ le_rfl
  apply (hn _ _).trans
  apply add_le_add le_rfl
  apply (hn _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ENNReal.ofReal_mul (abs_nonneg _),
    selectedMultiplierBulkDensity,mul_add,τ,le_refl]

lemma measurable_vec_clm_apply {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω→Vec→L[ℝ]Vec} {f : Ω→Vec} (hW : Measurable W) (hf : Measurable f) :
    Measurable (fun p=>W p (f p)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp (hW.prodMk hf)

lemma PhaseFlowOn.selectedMultiplierBulkDensity_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    Measurable (selectedMultiplierBulkDensity s F.flow zX T Q W) := by
  have hWt := hW
  exact ((measurable_vec_clm_apply hWt (F.actualLabelCutoffCost_measurable hs zX Q)).norm.ennreal_ofReal).add
    ((measurable_vec_clm_apply hWt ((F.selectedCutoff_measurable zX Q).smul
      (F.actualLabelRemainder_measurable hs zX))).norm.ennreal_ofReal)

lemma PhaseFlowOn.selectedMultiplierWeightDensity_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    Measurable (selectedMultiplierWeightDensity s F.flow zX T Q ψ W) := by
  exact ((measurable_vec_clm_apply hW
    ((F.labelWeight_measurable zX Q (measurable_deriv ψ)).smul
      (F.actualLabelRatePrimitive_measurable hs zX))).norm.ennreal_ofReal)

lemma PhaseFlowOn.selectedMultiplierMovingDensity_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} (hψ : Measurable ψ)
    {W' : ℝ→Vec→L[ℝ]Vec} (hW' : Measurable W') :
    Measurable (selectedMultiplierMovingDensity s F.flow zX T Q ψ W') := by
  exact ((measurable_vec_clm_apply (hW'.comp (F.labelReceiverTime_measurable zX))
    ((F.labelWeight_measurable zX Q hψ).smul
      (F.actualLabelRatePrimitive_measurable hs zX))).norm.ennreal_ofReal)

lemma PhaseFlowOn.selectedMultiplierCosts_integral_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} (hψ : Measurable ψ)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p‖ ≤
      (∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q ψ W p) +
      (∫⁻p,ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) +
      ∫⁻p,selectedMultiplierMovingDensity s F.flow zX T Q ψ W' p := by
  have hm₁ := F.selectedMultiplierWeightDensity_measurable hs zX Q ψ hW
  have hm₂ : Measurable (fun p : ℝ×Phase =>
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) := by
    convert ((hψ.comp (F.labelReceiverTime_measurable zX)).norm.ennreal_ofReal).mul
        (F.selectedMultiplierBulkDensity_measurable hs zX Q hW) using 1
    funext p
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs]
  have hm₁₂ : Measurable (fun p : ℝ×Phase =>
      selectedMultiplierWeightDensity s F.flow zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) := hm₁.add hm₂
  calc
    _ ≤ ∫⁻p,ENNReal.ofReal ‖selectedMultiplierCosts s F.flow zX T Q ψ W W' p‖ := by
      simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm
        (selectedMultiplierCosts s F.flow zX T Q ψ W W')
    _ ≤ ∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p +
      selectedMultiplierMovingDensity s F.flow zX T Q ψ W' p :=
        lintegral_mono (selectedMultiplierCosts_norm_le s F.flow zX T Q ψ W W')
    _ = _ := by rw [lintegral_add_left hm₁₂,lintegral_add_left hm₁]

lemma PhaseFlowOn.selectedMultiplierCosts_family_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p)))
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J) :
    (∑i∈S,ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q
      (directionWeight (a i) (b i) (ℓ i)) W W' p‖) ≤
      (∑i∈S,∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q
        (directionWeight (a i) (b i) (ℓ i)) W p) +
      (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
        (selectedMultiplierBulkDensity s F.flow zX T Q W) p) +
      ∑i∈S,∫⁻p,selectedMultiplierMovingDensity s F.flow zX T Q
        (directionWeight (a i) (b i) (ℓ i)) W' p := by
  classical
  have hi := Finset.sum_le_sum (fun i (_hi : i∈S) =>
    F.selectedMultiplierCosts_integral_bound hs zX Q
      (directionWeight_lipschitz (a i) (b i) (ℓ i)).continuous.measurable (W':=W') hW)
  simp only [Finset.sum_add_distrib] at hi
  exact hi.trans (add_le_add (add_le_add le_rfl
    (directionWeight_family_label_kernel volume S a b ℓ hℓ hlen hdis J hcell
      (labelReceiverTime F.flow zX T)
      (selectedMultiplierBulkDensity s F.flow zX T Q W))) le_rfl)

lemma unselected_multiplier_family_bound (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (Q : Set (Fin 4→ℕ)) (W : ℝ→Vec→L[ℝ]Vec)
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J) :
    (∑i∈S,ENNReal.ofReal ‖∫p,W (labelReceiverTime α zX T p)
      (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)‖) ≤
      ∫⁻p,{p : ℝ×Phase | labelReceiverTime α zX T p∈J}.indicator
        (fun p=>ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
          ((1-labelSelectedCutoff α zX T Q p) • actualLabelSignedForce s α zX T p)‖) p := by
  apply (Finset.sum_le_sum (fun i (_hi : i∈S) => by
    simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm
      (fun p=>W (labelReceiverTime α zX T p)
        (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)))).trans
  have he (i : ι) (p : ℝ×Phase) :
      ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
        (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)‖ =
      ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) (labelReceiverTime α zX T p)| *
        ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
          ((1-labelSelectedCutoff α zX T Q p) • actualLabelSignedForce s α zX T p)‖ := by
    rw [unselectedLabelSignedForce,smul_comm,map_smul,norm_smul,Real.norm_eq_abs,
      ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [←ofReal_norm,he]
  exact directionWeight_family_label_kernel volume S a b ℓ hℓ hlen hdis J hcell
    (labelReceiverTime α zX T) _

lemma measurable_angularMultiplierCLM (w : ℝ) : Measurable (angularMultiplierCLM w) := by
  apply measurable_of_continuousOn_compl_singleton (0:Vec)
  intro v hv
  exact (contDiffAt_angularMultiplierCLM w (by simpa using hv) (k:=1) (by simp)).continuousAt.continuousWithinAt

lemma PhaseFlowOn.measurable_labelAngularMultiplier {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (w : ℝ) :
    Measurable (fun p : ℝ×Phase=>angularMultiplierCLM w
      (F.flow zX (labelReceiverTime F.flow zX T p)).2) := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hm := (measurable_angularMultiplierCLM w).comp
    (hV.measurable.comp (F.labelReceiverTime_measurable zX))
  convert hm using 1
  funext p
  simp only [Function.comp_apply,prefixFlow,prefixClamp_eq (F.labelReceiverTime_mem hT zX p)]

lemma SmoothClassicalPrefix.actual_angular_family_bound {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hJ : J⊆Icc 0 T) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    (∑i∈S,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖) ≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       ((∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
            ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖) p) +
        (∑i∈S,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
          Q (directionWeight (a i) (b i) (ℓ i)) G z‖) +
        (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) +
        (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (selectedMultiplierBulkDensity s F.flow zX T Q G) p) +
        ∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) := by
  classical
  dsimp only
  let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
  let G' := fun t=>angularDerivativeCLM w (F.flow zX t).2
    (lorentzField s.E s.B (t,F.flow zX t)).2
  let ψ := fun i=>directionWeight (a i) (b i) (ℓ i)
  have hsupport i (hi : i∈S) : tsupport (ψ i)⊆J :=
    (directionWeight_tsupport (hℓ i hi) (hlen i hi)).trans (hcell i hi)
  have hψT i (hi : i∈S) : ψ i T=0 := by
    by_contra hn
    have hin := directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hn
    have hab : a i≤b i := by linarith only [hℓ i hi,hlen i hi]
    exact (not_lt_of_ge (hJ (hcell i hi ⟨hab,le_rfl⟩)).2) hin.2
  have hn (x y : Vec) : ENNReal.ofReal ‖x+y‖ ≤ ENNReal.ofReal ‖x‖+ENNReal.ofReal ‖y‖ := by
    rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  have hpoint i (hi : i∈S) :
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ i t • G t
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        (ENNReal.ofReal ‖∫p,G (labelReceiverTime F.flow zX T p)
            (unselectedLabelSignedForce s F.flow zX T Q (ψ i) p)‖ +
         ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q (ψ i) G z‖ +
         ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q (ψ i) G G' p‖) := by
    rw [hs.actual_angular_decomposition hT hw F zX Q (directionWeight_lipschitz _ _ _)
      (fun t _=>by rw [abs_of_nonneg (directionWeight_bounds (hℓ i hi) (hlen i hi)).1];
                   exact (directionWeight_bounds (hℓ i hi) (hlen i hi)).2)
      (hψT i hi) ((hsupport i hi).trans hJ) (fun t ht=>hband t (hsupport i hi ht))]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹),
      ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
    apply mul_le_mul' le_rfl
    exact (hn _ _).trans (add_le_add (hn _ _) le_rfl)
  have hi := Finset.sum_le_sum hpoint
  rw [←Finset.mul_sum] at hi
  simp only [Finset.sum_add_distrib] at hi
  have hu := unselected_multiplier_family_bound s F.flow zX T Q G S a b ℓ hℓ hlen hdis J hcell
  have hc := F.selectedMultiplierCosts_family_bound hs.selectedDirectionEnergyPrefix zX Q
    (W:=G) (W':=G') (F.measurable_labelAngularMultiplier hs.selectedDirectionEnergyPrefix hT zX w)
    S a b ℓ hℓ hlen hdis J hcell
  apply hi.trans
  apply mul_le_mul' le_rfl
  have hh := add_le_add (add_le_add hu (le_refl (∑i∈S,ENNReal.ofReal ‖∫z : Phase,
    selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q (ψ i) G z‖))) hc
  simpa only [selectedAngularWeightCost,selectedAngularMovingCost,
    selectedMultiplierWeightDensity,selectedMultiplierMovingDensity,add_assoc,G,G',ψ] using hh

end RVM

end

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.measurable_labelConeKernel_localBorel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable ((coneKernelInterior T).indicator A)) :
    Measurable (labelConeKernel s F.flow zX T A) := by
  rw [←F.labelConeKernel_interior_indicator zX A,F.labelConeKernel_eq_pullback hs zX]
  exact F.measurable_phaseTimePullback (F.measurable_arrivalConeKernel_borel hs zX hA)

lemma PhaseFlowOn.partialCutoffLabelCost_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) :
    Measurable (partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T)) := by
  classical
  rw [F.partialCutoffLabelCost_eq_normalised zX Q H]
  exact F.measurable_labelConeKernel_localBorel hs zX
    ((F.normalisedPartialCutoff_continuousOn zX Q hH).measurable_piecewise
      continuousOn_const (measurableSet_coneKernelInterior T))

lemma PhaseFlowOn.cutoff_label_integral_split {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (actualLabelCutoffCost s F.flow zX T Q p)‖)≤
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffGeometryTangent (branchTime F.flow zX p.2 T p.1-p.1) (branchRate F.flow zX p.2 T p.1)
          (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2) (velocity (F.flow p.2 p.1).2)
          (branchDirection F.flow zX p.2 T p.1)) p)‖)+
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q
        (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
          (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖) := by
  have hWt := hW.comp (F.labelReceiverTime_measurable zX)
  have hm (H : ConeKernelState→CutoffState) (hH : ContinuousOn H (coneKernelInterior T)) :=
    (measurable_vec_clm_apply hWt (F.partialCutoffLabelCost_measurable hs zX Q hH)).norm.ennreal_ofReal
  have hs' := hm _ (F.coneSourceCutoffTangent_continuousOn hs zX)
  have hg' := hm _ (F.coneGeometryCutoffTangent_continuousOn hs zX)
  have hr' := hm _ (F.coneReceiverCutoffTangent_continuousOn hs zX)
  rw [coneSourceCutoffTangent_pullback] at hs'
  rw [coneGeometryCutoffTangent_pullback] at hg'
  rw [coneReceiverCutoffTangent_pullback] at hr'
  simp only [Function.comp_apply] at hs' hg' hr'
  rw [←lintegral_add_left hs' _,←lintegral_add_right _ hr']
  apply lintegral_mono
  intro p
  dsimp only
  rw [actualLabelCutoffCost_split,map_add,map_add]
  have hn (x y : Vec) : ENNReal.ofReal ‖x+y‖≤ENNReal.ofReal ‖x‖+ENNReal.ofReal ‖y‖ := by
    rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  exact (hn _ _).trans (add_le_add (hn _ _) le_rfl)

lemma Admissible.direction_receiverCutoff_label_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0<P → 1≤Real.log (2+P) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
            (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.actual_receiverCutoff_label_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨C*Cn^2,by positivity,?_⟩
  intro s T F hs h0 hT zX J w P hw hJ hJT hP hL hq hW hsource
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hEuler (σ : ℝ) (hσ : σ∈Icc 0 T) (z : Phase) (hf : s.f (σ,z)≠0) :
      1024*q z.2≤(2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (F.eulerian_supported_momentum hs hsource hσ z.1 z.2 hf)
      (by norm_num : (0:ℝ)≤1024)).trans hN
  apply (hbound s T F hs h0 hT zX J w (1/1024) N (directionSelection T) hw hJ hJT
    (by norm_num) (by norm_num) (fun k hk=>hk) hq hW hEuler).trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2/w := by gcongr
    _ = _ := by ring

lemma Admissible.direction_selected_bulk_log_bound {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl Cg Ck : ℝ,0≤Ce ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ck ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → T≤T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T (directionSelection T)
        ((Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)) p)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2)+
      ENNReal.ofReal (Cg*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨Ce,Cf,Cl,hCe,hCf,hCl,hsourcecost⟩ := hd₀.direction_sourceCutoff_label_log_bound T₀
  obtain ⟨Cg,hCg,hgeom⟩ := hd₀.direction_geometryCutoff_label_log_bound
  obtain ⟨Cr,hCr,hrem⟩ := hd₀.direction_remainder_label_log_bound
  obtain ⟨Ck,hCk,hrec⟩ := hd₀.direction_receiverCutoff_label_log_bound
  refine ⟨Ce,Cf,Cl,Cg+Cr,Ck+Cr,hCe,hCf,hCl,by positivity,by positivity,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hW HX HZ
  dsimp only
  have hwc : Measurable ((Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)) :=
    (F.prefixAngular_regular hs hT hw zX).1.measurable.indicator measurableSet_Icc
  have hsc := hsourcecost s T F hs hT hTT h0 zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hW HX HZ
  have hgc := hgeom s T F hs hT h0 zX S a b w M A P hw hS hS0 ha hb hJI hM hA (zero_lt_one.trans_le hP) hL hwP hPw hsource hq hW HX HZ
  have hrc := hrec s T F hs h0 hT zX (Icc a b) w P hw measurableSet_Icc (Icc_subset_Icc ha hb) (zero_lt_one.trans_le hP) hL hq hW hsource
  have hrm := hrem s T F hs hT h0 zX S a b w M A P hw hS hS0 ha hb hJI hM hA (zero_lt_one.trans_le hP) hL hwP hPw hsource hq hW HX HZ
  have hcut := (F.cutoff_label_integral_split hs zX (directionSelection T) hwc).trans
    (add_le_add (add_le_add hsc hgc) hrc)
  have hmeas : Measurable (fun p : ℝ×Phase=>ENNReal.ofReal ‖((Icc a b).indicator
      (prefixAngularMultiplier s F.flow T w hw zX) (labelReceiverTime F.flow zX T p))
        (actualLabelCutoffCost s F.flow zX T (directionSelection T) p)‖) :=
    (measurable_vec_clm_apply (hwc.comp (F.labelReceiverTime_measurable zX))
      (F.actualLabelCutoffCost_measurable hs zX (directionSelection T))).norm.ennreal_ofReal
  simp only [selectedMultiplierBulkDensity]
  rw [lintegral_add_left hmeas]
  apply (add_le_add hcut hrm).trans_eq
  have hE : 0≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hG : ENNReal.ofReal ((Cg+Cr)*max 1 T*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)=
      ENNReal.ofReal (Cg*max 1 T*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      ENNReal.ofReal (Cr*max 1 T*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hK : ENNReal.ofReal ((Ck+Cr)*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)=
      ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)+
      ENNReal.ofReal (Cr*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hG,hK,mul_add]
  ring_nf

lemma relativeRepresentative_momentum_subset (T w : ℝ) (k : Fin 4→ℕ) (j : ℕ)
    (n W : Vec) : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n (velocity W) ⊆
      coneBinMomentumSet (representativeClosedBin T w k) n (velocity W) := by
  intro v hv
  exact ⟨hv.1,hv.2.1,velocity_deficit_mem_unit2 v W⟩

lemma relativeRepresentative_density_le (s : Solution) (X V : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (j : ℕ) (z : ConeCoordinate) :
    physicalBinDensity s X V (relativeRepresentativeClosedBin T w k j) z.1 z.2.1 z.2.2 ≤
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
  exact lintegral_mono' (Measure.restrict_mono
    (relativeRepresentative_momentum_subset T w k j z.2.2.1 (V z.1)) le_rfl) (fun _ => le_rfl)

lemma transport_small_central_coefficient {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ)
    (hφ : 0<φ) (hsmall : θ ≤ φ/16) (hpθ : 1 ≤ p*θ) :
    128*(θ+φ)/((p/128)^2*θ^3) ≤ φ⁻¹*(78400000*φ^2/θ) := by
  have hsq : 1 ≤ (p*θ)^2 := one_le_pow₀ hpθ
  apply (div_le_iff₀ (by positivity : 0<(p/128)^2*θ^3)).mpr
  have he : φ⁻¹*(78400000*φ^2/θ)*((p/128)^2*θ^3)=
      (78400000/16384:ℝ)*φ*(p*θ)^2 := by field_simp; ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsq hφ.le
  nlinarith only [hsmall,hh,hφ]

lemma PhaseFlowOn.direct_transport_small_central {s : Solution} {T a b w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (k : Fin 4→ℕ) (j : ℕ) (ha : 0 ≤ a) (hb : b ≤ T)
    (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16)
    (hpθ : 1  ≤  sourceRepresentative (k 0)*cappedRepresentative (k 1)) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let B := relativeRepresentativeClosedBin T w k j
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (cappedRepresentative (k 2))⁻¹ *
        (ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
          (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
            z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) := by
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := relativeRepresentativeClosedBin T w k j
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hα := (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk (continuous_const (y:=zX)))
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hm : physicalBinMeasure V B (Icc a b)=physicalBinMeasure V (representativeClosedBin T w k) (Icc a b) := rfl
  rw [←mul_assoc,←ENNReal.ofReal_mul (inv_nonneg.mpr hφ.le),
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←hm]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable B measurableSet_Icc)] with z hz
  have hrad : 0<z.1-z.2.1 := (representativeClosedBin_radius_pos T w k).trans_le hz.2.2.1.1
  have hn := physicalDirectTransportDensity_bound (s:=s) (X:=X) (V:=V) (B:=B) hrad
    (by positivity : 0<p/128) hθ hφ.le le_rfl le_rfl le_rfl hz.2.2.2.2.2
    (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ _)
  apply hn.trans
  exact mul_le_mul'
    (ENNReal.ofReal_le_ofReal (transport_small_central_coefficient hp hθ hφ hsmall hpθ))
    (relativeRepresentative_density_le s X V T w k j z)

lemma Admissible.direct_transport_small_stable_radii {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0 ≤ A → 0<P → 1 ≤  Real.log (2+P) →
      0<w → w ≤ P → sourceRepresentative np ≤ 128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 → 32 ≤ cappedRepresentative nφ*w →
      1  ≤  sourceRepresentative np*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_stable_radial_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hwφ hpθ HX HZ
  dsimp only
  have hφ : 0<cappedRepresentative nφ := cappedRepresentative_pos _
  have h := hbound s T F hs hT h0 zX S np nθ nφ a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hwφ HX HZ
  have hh (nr : ℕ) := F.direct_transport_small_central (w:=w) hs hT zX ![np,nθ,nφ,nr] j ha hb
    (by simpa using hsmall) (by simpa using hpθ)
  have hsum := ENNReal.tsum_le_tsum hh
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at hsum
  rw [ENNReal.tsum_mul_left] at hsum
  apply hsum.trans ((mul_le_mul' le_rfl h).trans ?_)
  rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hφ.le)]
  apply ENNReal.ofReal_le_ofReal
  have he : 0 ≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  field_simp
  exact le_rfl

lemma transport_low_receiver_coefficient {I p θ φ σ w P : ℝ}
    (hI : 0 ≤ I) (hp : 0 ≤ p) (hθ : 0<θ) (hφ : 0 ≤ φ) (hσ : 0 ≤ σ)
    (hφ1 : φ ≤ 1) (hpθ : 1 ≤ p*θ) (hw : 0 ≤ w) (hP : 0<P)
    (hwP : w ≤ P) (hIp : I ≤ (w/P)^2) (hpP : p ≤ 128*P) (hwφ : φ*w ≤ 32) :
    I*p*(min θ σ)^2*φ^2*(θ+φ)/θ^3 ≤ 524416*w := by
  have hν : 0 ≤ min θ σ := le_min hθ.le hσ
  have hsq : (min θ σ)^2 ≤ θ^2 := pow_le_pow_left₀ hν (min_le_left _ _) 2
  have hφsq : φ^2 ≤ 1 := pow_le_one₀ hφ hφ1
  have hinv : 1/θ ≤ p := (div_le_iff₀ hθ).mpr hpθ
  have hIp1 : I*p ≤ 128*w := (mul_le_mul_of_nonneg_right hIp hp).trans
    (direction_interval_momentum_factor hP hp hw hpP hwP)
  have hIp2 : I*p^2 ≤ 16384*w^2 := by
    calc
      _  ≤  (w/P)^2*(128*P)^2 := by gcongr
      _ = _ := by field_simp; ring
  have hφw3 : w^2*φ^3 ≤ 32*w := by
    calc
      _ = w*(φ*w)*φ^2 := by ring
      _  ≤  w*32*1 := by gcongr
      _ = _ := by ring
  calc
    _  ≤  I*p*θ^2*φ^2*(θ+φ)/θ^3 := by gcongr
    _ = I*p*φ^2*(1+(1/θ)*φ) := by field_simp
    _  ≤  I*p*φ^2*(1+p*φ) := by gcongr
    _ = (I*p)*φ^2+(I*p^2)*φ^3 := by ring
    _  ≤  (128*w)*1+(16384*w^2)*φ^3 := by gcongr
    _ = 128*w+16384*(w^2*φ^3) := by ring
    _  ≤  128*w+16384*(32*w) := by gcongr
    _ = _ := by ring

lemma Admissible.direct_transport_low_receiver_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b I w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ I → 0 < I → 0<w → 0<P → w ≤ P →
      I ≤ (w/P)^2 → sourceRepresentative np ≤ 128*P →
      1 ≤ sourceRepresentative np*cappedRepresentative nθ → cappedRepresentative nφ*w ≤ 32 →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*max 1 T*w) := by
  obtain ⟨C,hC,hnear⟩ := hd₀.direct_transport_radius_near
  refine ⟨1048832*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b I w P hS hS0 ha hb hJI hI hw hP hwP hIw hpP hpθ hwφ
  dsimp only
  have hp : 0<sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
  have hcoef := transport_low_receiver_coefficient hI.le hp.le (cappedRepresentative_pos nθ)
    (cappedRepresentative_pos nφ).le (cappedRepresentative_pos j).le
    (cappedRepresentative_le_one nφ) hpθ hw.le hP hwP hIw hpP hwφ
  calc
    _ ≤ ∑'nr : ℕ,ENNReal.ofReal ((524416*C*w)*(max 1 T*cappedRepresentative nr)) := by
      apply ENNReal.tsum_le_tsum
      intro nr
      have hn := hnear s T F hs hT h0 zX S ![np,nθ,nφ,nr] j a b I w hS hS0 ha hb hJI hI
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk]
      calc
        _ = (C*(max 1 T*cappedRepresentative nr))*(I*sourceRepresentative np*
              (min (cappedRepresentative nθ) (cappedRepresentative j))^2*
              (cappedRepresentative nφ)^2*(cappedRepresentative nθ+cappedRepresentative nφ)/
              (cappedRepresentative nθ)^3) := by ring
        _ ≤ (C*(max 1 T*cappedRepresentative nr))*(524416*w) :=
          mul_le_mul_of_nonneg_left hcoef (mul_nonneg hC (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (cappedRepresentative_pos nr).le))
        _ = _ := by ring
    _ = _ := by
      rw [capped_linear_radius_sum (by positivity) (by positivity)]
      congr 1
      ring

lemma Admissible.direct_transport_sharp_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0 ≤ A → 0<P → 1 ≤ Real.log (2+P) →
      0<w → w ≤ P → sourceRepresentative np ≤ 128*P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C₁,hC₁,h₁⟩ := hd₀.direct_transport_remaining_all_radii
  obtain ⟨C₂,hC₂,h₂⟩ := hd₀.direct_transport_low_receiver_radii
  obtain ⟨C₃,hC₃,h₃⟩ := hd₀.direct_transport_small_stable_radii
  refine ⟨C₁+C₂+C₃,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP HX HZ
  dsimp only
  have he : 0 ≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hMa : 1 ≤ 1+16384*(M+Real.sqrt A) := by linarith only [hM,Real.sqrt_nonneg A]
  have he1 : 1 ≤ 1+∫x : Vec,totalEnergy s (0,x) := by linarith only [he]
  have hL1 : 1 ≤ Real.sqrt (Real.log (2+P)) := Real.one_le_sqrt.mpr hL
  have hH : 1 ≤ max 1 T := le_max_left _ _
  have hI : 0<(w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have absorb (C : ℝ) (hC : 0 ≤ C) (hCc : C ≤ C₁+C₂+C₃) :
      C*max 1 T*w ≤ (C₁+C₂+C₃)*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P)) := by
    calc
      _ = C*1*1*max 1 T*w*1 := by ring
      _ ≤ _ := by gcongr
  by_cases hpθ : 1 ≤ sourceRepresentative np*cappedRepresentative nθ
  · by_cases hsmall : cappedRepresentative nθ ≤ cappedRepresentative nφ/16
    · by_cases hstable : 32 ≤ cappedRepresentative nφ*w
      · apply (h₃ s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hstable hpθ HX HZ).trans
        apply ENNReal.ofReal_le_ofReal
        calc
          _ = C₃*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*1*w*Real.sqrt (Real.log (2+P)) := by ring
          _ ≤ _ := by gcongr; linarith only [hC₁,hC₂]
      · apply (h₂ s T F hs hT h0 zX S np nθ nφ j a b ((w/P)^2) w P hS hS0 ha hb hab hI hw hP hwP le_rfl hpP hpθ (lt_of_not_ge hstable).le).trans
        exact ENNReal.ofReal_le_ofReal (absorb C₂ hC₂ (by linarith only [hC₁,hC₃]))
    · apply (h₁ s T F hs hT h0 zX S np nθ nφ j a b ((w/P)^2) w P hS hS0 ha hb hab hI hw hP hwP le_rfl hpP (by linarith only [hsmall])).trans
      exact ENNReal.ofReal_le_ofReal (absorb C₁ hC₁ (by linarith only [hC₂,hC₃]))
  · have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
        (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
        (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) (Icc a b))=0 := by
      exact physicalDirectTransport_integral_geometry_zero s hV measurableSet_Icc hpθ
    simp_rw [hz,tsum_zero]
    exact bot_le

lemma Admissible.direct_transport_sharp_physical_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0≤A → 1≤Real.log (2+P) → 1≤w → 0<P → w≤P →
      8192*P≤(2:ℝ)^N →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directTransportTriangleKernel V) p
        ∂trianglePhaseMeasure) ≤ (N:ℝ≥0∞)^4*ENNReal.ofReal (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_transport_sharp_all_radii
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hJI hM hA hL hw hP hwP hN hPbound hW HX HZ
  dsimp only
  have hα : Continuous (fun t : ℝ => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJT : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband : ∀t∈Icc a b,q (prefixFlow F.flow T zX t).2∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [prefixFlow,prefixClamp_eq (hJT ht)] using hW t ht
  apply F.directTriangle_family_estimate hs hT hP.le hwP N hN hPbound
    (fun t => (prefixFlow F.flow T zX t).1) (fun t => (prefixFlow F.flow T zX t).2)
    hα.fst.measurable hα.snd.measurable (Icc a b) measurableSet_Icc hband
    (directTransportTriangleKernel (fun t => (prefixFlow F.flow T zX t).2))
    (measurable_directTransportTriangleKernel hα.snd.measurable)
    (physicalDirectTransportDensity s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2)) (ENNReal.ofReal (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P))))
    (fun B z hz=>directTransportTriangle_bin_bound (s:=s)
      (X:=fun t=>(prefixFlow F.flow T zX t).1) (V:=fun t=>(prefixFlow F.flow T zX t).2)
      (T:=T) hJT B hz)
  intro i hi
  exact hbound s T F hs hT h0 zX S (i 0).val (i 1).val (i 2).val (i 3).val a b w M A P
    hS hS0 ha hb hJI hM hA hP hL (zero_lt_one.trans_le hw) hwP hi HX HZ

lemma Admissible.direct_transport_sharp_physical_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0≤A → 1≤w → 1≤P → w≤P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directTransportTriangleKernel V) p
        ∂trianglePhaseMeasure) ≤ ENNReal.ofReal (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_transport_sharp_physical_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  refine ⟨C*Cn^4,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hJI hM hA hw hP hwP hL hPbound hW HX HZ
  dsimp only
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  apply (hbound s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hJI hM hA hL hw
    (zero_lt_one.trans_le hP) hwP hN hPbound hW HX HZ).trans
  apply (ennreal_count_four_bound hCn (zero_le_one.trans hL) hNc
    (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P)))).trans
  apply ENNReal.ofReal_le_ofReal
  have he : 0≤∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hsqrt : Real.sqrt (Real.log (2+P))≤Real.log (2+P) := (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith only [hL]⟩
  calc
    _ ≤ Cn^4*(Real.log (2+P))^4*(C*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.log (2+P)) := by gcongr
    _ = _ := by ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direction_lorentz_log_bound {d : Datum} (hd₀ : Admissible d)
    (T : ℝ) (hT : 0≤T) :
    ∃ Cb Ct Cs : ℝ,0≤Cb ∧ 0≤Ct ∧ 0≤Cs ∧
    ∀ (s : Solution) (F : PhaseFlowOn s.E s.B T), SmoothClassicalPrefix d s T →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
          cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖) ≤
      ENNReal.ofReal (Cb*(b-a)) + ENNReal.ofReal (4*Real.pi)⁻¹ *
       (ENNReal.ofReal (Ct*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*(Real.log (2+P))^5) +
        ENNReal.ofReal (Cs*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5)) := by
  obtain ⟨Cb,hCb,hdatum⟩ := hd₀.supported_boundary_force_bound T hT
  obtain ⟨Ct,hCt,htrans⟩ := hd₀.direct_transport_sharp_physical_log_bound
  obtain ⟨Cs,hCs,hsource⟩ := hd₀.direct_source_physical_log_bound
  refine ⟨Cb,Ct,Cs,hCb,hCt,hCs,?_⟩
  intro s F hs zX S a b w M A P hzX hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPbound hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hcon := (F.continuous_prefixFlow hs.selectedDirectionEnergyPrefix hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcon.fst.measurable
  have hV : Measurable V := hcon.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hS0' : tsupport (fun z=>s.f (0,z))⊆S := by rw [hdata]; exact hS0
  have hDb : ∀t∈Ioo 0 T∩Icc a b,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤Cb := by
    intro t ht
    dsimp only [X,V,prefixFlow]
    rw [prefixClamp_eq (hJ ht.2)]
    exact hdatum s.E s.B F zX hzX t ⟨ht.1.1,ht.1.2.le⟩
  have hraw : (∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,(F.flow zX t).1)+
      cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [X,V,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hraw]
  apply (hs.direct_lorentz_triangle_bound hT X V hX hV measurableSet_Icc hJ Cb hCb hDb).trans
  have hD : ENNReal.ofReal Cb*volume (Icc a b)=ENNReal.ofReal (Cb*(b-a)) := by
    rw [Real.volume_Icc,ENNReal.ofReal_mul hCb]
  rw [hD]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  exact add_le_add
    (htrans s T F hs.selectedDirectionEnergyPrefix hT hs.initial_f zX S a b w M A P hS hS0' ha hb hJI hM hA hw hP hwP hL hPbound hW HX HZ)
    (hsource s T F hs.selectedDirectionEnergyPrefix hT hs.initial_f zX S a b w M A P hS hS0' ha hb hab hJI hM hA hP hL hw hwP
      hPbound hW HX HZ)

end RVM

end

end OAI
