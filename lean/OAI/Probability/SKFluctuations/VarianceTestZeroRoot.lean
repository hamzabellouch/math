import Mathlib
import OAI.Probability.SKFluctuations.OrderedSKCumulativeChord

namespace OAI

/-! Variance Test Zero Root. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
theorem varianceTest_zero_root (F A : (ι → ℝ) → ℝ) (q x : ι → ℝ) :
    varianceTest 0 F A q x =
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i))) A x :=
  shiftedMean_zero F A x

 

theorem dynamic_zeroContinuation_continuous {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] {A : P → (ι → ℝ) → ℝ} {K : ℝ}
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hbA : ∀ p y, |A p y| ≤ K) {q x : P → ι → ℝ} (hq : Continuous q) (hx : Continuous x) :
    Continuous (fun p => zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q p i))) (A p) (x p)) := by
  have hh := dynamic_varianceTest_continuous (fun _ : P => LipschitzWith.const (0:ℝ))
    (by fun_prop) hcA hbA 0 hq hx
  simpa only [varianceTest_zero_root] using hh

 

theorem hasDerivAt_dynamic_zeroContinuation {n : ℕ}
    {F D : ℝ → (Fin (n+1) → ℝ) → ℝ}
    {G H : ℝ → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ t, LipschitzWith C (F t))
    (hG : ∀ t i, BddSmooth 0 (G t i)) (hH : ∀ t i, BddSmooth 0 (H t i))
    (hcH : ∀ i, Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 i p.2))
    (hcD : Continuous (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hbH : ∀ i, AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => H p.1 i p.2))
    (hbD : AbsBounded (fun p : ℝ × (Fin (n+1) → ℝ) => D p.1 p.2))
    (hd : ∀ s x v t, HasDerivAt (fun r : ℝ => F s (x+r • v))
      (∑ i, v i*G s i (x+t • v)) t)
    (hd₁ : ∀ s i x t, HasDerivAt (fun r : ℝ => G s i (x+r • Pi.single i 1))
      (H s i (x+t • Pi.single i 1)) t)
    {l r : ℝ} (hdF : ∀ s ∈ Ioo l r, ∀ y, HasDerivAt (fun q => F q y) (D s y) s)
    (q d : Fin (n+1) → ℝ) {t : ℝ}
    (ht : t ∈ Ioo l r) (hqt : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+s*d i))) (F s) x)
      ((∑ i, (d i/2)*zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i))) (H t i) x)+
        zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i))) (D t) x) t := by
  obtain ⟨KD,hKD,bD⟩ := hbD
  choose KH hKH bH using hbH
  let Q : ℝ × ℝ → Fin (n+1) → ℝ := fun p i => q i+p.1*d i
  have hQ : Continuous Q := continuous_pi fun i => continuous_const.add (continuous_fst.mul continuous_const)
  have hc₁ : Continuous (fun p : ℝ × ℝ => ∑ i, (d i/2)*
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (Q p i))) (H p.2 i) x) := by
    apply continuous_finsetSum
    intro i _
    exact (dynamic_zeroContinuation_continuous (P := ℝ × ℝ)
      (A := fun p y => H p.2 i y) (q := Q) (x := fun _ => x)
      ((hcH i).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => bH i (p.2,y)) hQ continuous_const).const_mul (d i/2)
  have hc₂ : Continuous (fun p : ℝ × ℝ =>
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (Q p i))) (D p.2) x) :=
    dynamic_zeroContinuation_continuous (P := ℝ × ℝ)
      (A := fun p y => D p.2 y) (q := Q) (x := fun _ => x)
      (hcD.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun p y => bD (p.2,y)) hQ continuous_const
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (hqt i))
  have hc₃ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
          (Real.toNNReal (q i+s*d i))) (F p.2) x)
        (∑ i, (d i/2)*zeroContinuation (Measure.pi fun i => gaussianReal 0
          (Real.toNNReal (q i+p.1*d i))) (H p.2 i) x) p.1 := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hp] with p hp
    exact hasDerivAt_signed_zeroContinuation (hF p.2) (hG p.2) (hH p.2) (hd p.2) (hd₁ p.2) q d hp x
  have hparam : ParametricRegular l r KD F D :=
    ⟨hKD,fun s _ => ⟨C,hF s⟩,
      fun s _ => hcD.comp (continuous_const.prodMk continuous_id),
      fun s _ y => bD (s,y),hdF⟩
  have hc₄ : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,t),
      HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
          (Real.toNNReal (q i+p.1*d i))) (F s) x)
        (zeroContinuation (Measure.pi fun i => gaussianReal 0
          (Real.toNNReal (q i+p.1*d i))) (D p.2) x) p.2 := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht)] with p hp
    exact (hparam.root _).derivative p.2 hp x
  have hchain := hasDerivAt_bivariate_chain
    (f := fun a b => zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q i+a*d i))) (F b) x)
    (f₁ := fun a b => ∑ i, (d i/2)*zeroContinuation (Measure.pi fun j => gaussianReal 0
      (Real.toNNReal (q j+a*d j))) (H b i) x)
    (f₂ := fun a b => zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q i+a*d i))) (D b) x)
    hc₃ hc₄ hc₁.continuousAt hc₂.continuousAt (hasDerivAt_id t) (hasDerivAt_id t)
  simpa only [id_eq,mul_one] using hchain

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_affine_variation {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (ss : List (SignedStep (Fin (n+1))))
    (q d : Fin (n+1) → ℝ) {l r : ℝ}
    (ha : OrderedSteps 0 (affineSteps ss 0))
    (hq : ∀ st ∈ ss, ∀ t ∈ Ioo l r, ∀ i, 0 < st.2.1 i+t*st.2.2 i)
    {t : ℝ} (ht : t ∈ Ioo l r) (hqt : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+s*d i))) (gaussianHierarchy w φ (affineSteps ss s)) x)
      ((∑ i, (d i/2)*zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i)))
        (fun y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1)) x)+
        zeroContinuation (Measure.pi fun i => gaussianReal 0
          (Real.toNNReal (q i+t*d i))) (affineVariation w φ ss t) x) t := by
  obtain ⟨C,hF⟩ := affineHierarchy_lipschitz hw φ
  have ho := affineSteps_ordered ss ha
  have hD := affineVariation_regular hw φ ss ha
  apply hasDerivAt_dynamic_zeroContinuation
    (F := fun t => gaussianHierarchy w φ (affineSteps ss t))
    (G := fun t i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) (affineSteps ss t))
    (H := fun t i y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1))
    (D := affineVariation w φ ss)
    (hF ss ha)
    (fun t i => gaussianHierarchyMean_smooth hw φ _ _ (ho t) 0)
    (fun t i => gaussianHierarchyResponse_smooth hw φ _ _ _ (ho t) 0)
    (fun i => affineHierarchyHessian_continuous hw φ _ ss ha) hD.1
    (fun i => affineHierarchyHessian_absBounded hw φ _ ss ha) hD.2
    (fun s y v u => ?_) (fun s i y u => ?_)
    (fun s hs y => gaussianHierarchy_affine_variation hw φ ss ha hq hs y) q d ht hqt x
  · rw [← gaussianHierarchyMean_feature_components hw φ _ (ho s) v (y+u • v)]
    exact gaussianHierarchy_hasDerivAt hw φ _ (ho s) y v u
  · exact gaussianHierarchyMean_hasDerivAt hw φ _ _ (ho s) y _ u

 

theorem rootedHierarchy_corrected_affine_variation {n : ℕ} {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (Q : SignedStep (Fin (n+1)) → ℝ) (ss : List (SignedStep (Fin (n+1))))
    (q d : Fin (n+1) → ℝ) {Q₀ l r : ℝ}
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = Q st)
    (hQ₀ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q₀)
    (ha : OrderedSteps 0 (affineSteps ss 0))
    (hq : ∀ st ∈ ss, ∀ t ∈ Ioo l r, ∀ i, 0 < st.2.1 i+t*st.2.2 i)
    {t : ℝ} (ht : t ∈ Ioo l r) (hqt : ∀ i, 0 < q i+t*d i) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+s*d i))) (gaussianHierarchy w φ (affineSteps ss s)) x-
          (Q₀+(ss.map Q).sum)*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i)))
        (pathKernelPenalty w φ (featureKernel φ d) 0 ss t) x) t := by
  have ho := affineSteps_ordered ss ha t
  let ν := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+t*d i))
  let K := featureKernel φ d
  let P := kernelPenalty w φ K 0 (affineSteps ss t)
  let R := pathKernelPenalty w φ K 0 ss t
  let H := fun i y => gaussianHierarchyHessian w φ (affineSteps ss t) y (Pi.single i 1) (Pi.single i 1)
  have hP : BddSmooth 0 P := kernelPenalty_smooth hw φ K _ ho 0
  have hR : BddSmooth 0 R := pathKernelPenalty_smooth hw φ K ss ha t 0
  have hH (i) : BddSmooth 0 (H i) := gaussianHierarchyResponse_smooth hw φ _ _ _ ho 0
  have heH : (fun y => ∑ i, d i*H i y) = fun y => Q₀-P y := by
    funext y
    have he := weighted_feature_trace_telescope hw φ d hQ₀ _ ho y
    rw [← kernelPenalty_weighted_features hw φ (fun i => Pi.single i 1) d _ ho] at he
    dsimp only [H,P,K,featureKernel,gaussianHierarchyHessian]
    change _ = Q₀-kernelPenalty w φ (fun σ τ => ∑ i, d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)) 0 (affineSteps ss t) y
    simpa only [zero_mul,add_zero] using he
  have heD := funext fun y => affineVariation_kernel_telescope hw φ Q ss hQ K ha t y
  have hroot : (∑ i, (d i/2)*zeroContinuation ν (H i) x) =
      Q₀/2-(1/2:ℝ)*zeroContinuation ν P x := by
    have hi (i) : Integrable (fun z => d i*H i (x+z)) ν :=
      ((hH i).integrable_zero_shift x).const_mul (d i)
    have he := congrArg (fun A => zeroContinuation ν A x) heH
    simp only [zeroContinuation] at he ⊢
    rw [integral_finsetSum _ (fun i _ => hi i),
      integral_sub (integrable_const _) (hP.integrable_zero_shift x)] at he
    simp only [integral_const_mul,integral_const,probReal_univ,one_smul] at he
    calc
      _ = (1/2:ℝ)*(∑ i, d i*∫ z, H i (x+z) ∂ν) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [he]; ring
  have hder := (rootedHierarchy_affine_variation hw φ ss q d ha hq ht hqt x).sub
    (((hasDerivAt_id t).const_mul (Q₀+(ss.map Q).sum)).div_const 2)
  change HasDerivAt _ ((∑ i, (d i/2)*zeroContinuation ν (H i) x)+
    zeroContinuation ν (affineVariation w φ ss t) x-_) _ at hder
  rw [hroot,heD] at hder
  have hev : zeroContinuation ν
      (fun y => (ss.map Q).sum/2+(1/2:ℝ)*P y-(1/2:ℝ)*R y) x =
      (ss.map Q).sum/2+(1/2:ℝ)*zeroContinuation ν P x-(1/2:ℝ)*zeroContinuation ν R x := by
    simp only [zeroContinuation]
    have hiP : Integrable (fun z => P (x+z)) ν := hP.integrable_zero_shift x
    have hiR : Integrable (fun z => R (x+z)) ν := hR.integrable_zero_shift x
    have hiA : Integrable (fun z => (ss.map Q).sum/2+(1/2:ℝ)*P (x+z)) ν :=
      (integrable_const ((ss.map Q).sum/2)).add (hiP.const_mul (1/2:ℝ))
    rw [integral_sub hiA (hiR.const_mul (1/2:ℝ)),
      integral_add (integrable_const ((ss.map Q).sum/2)) (hiP.const_mul (1/2:ℝ)),
      integral_const_mul,integral_const_mul]
    simp
  rw [hev] at hder
  exact hder.congr_deriv (by change _ = -(1/2:ℝ)*zeroContinuation ν R x; ring)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype S] [Nonempty S]

omit [DecidableEq ι] [DecidableEq κ] [Nonempty S] in
theorem gaussianHierarchyMean_reindex_steps (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι)) :
    gaussianHierarchyMean w (reindexFeature e φ) A (reindexSteps e steps) =
      fun x => gaussianHierarchyMean w φ A steps (coordinateEquiv e x) := by
  induction steps with
  | nil => rfl
  | cons st steps ih =>
    funext x
    change shiftedMean _ _ (gaussianHierarchy w (reindexFeature e φ) (reindexSteps e steps))
      (gaussianHierarchyMean w (reindexFeature e φ) A (reindexSteps e steps)) x = _
    rw [ih,gaussianHierarchy_reindex_steps]
    exact shiftedMean_reindex e st.2 st.1 _ _ x

omit [DecidableEq ι] [DecidableEq κ] [Nonempty S] in
theorem hierarchyPairMean_reindex_steps (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι)) :
    hierarchyPairMean w (reindexFeature e φ) K (reindexSteps e steps) =
      fun x => hierarchyPairMean w φ K steps (coordinateEquiv e x) := by
  funext x
  simp only [hierarchyPairMean,hierarchyAtom,gaussianHierarchyMean_reindex_steps]

omit [Nonempty S] in
theorem pathKernelPenalty_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (a : ℝ)
    (ss : List (SignedStep ι)) (t : ℝ) :
    pathKernelPenalty w (reindexFeature e φ) K a (reindexSignedSteps e ss) t =
      fun x => pathKernelPenalty w φ K a ss t (coordinateEquiv e x) := by
  induction ss generalizing a K with
  | nil => exact congrArg (fun f => fun x => (1-a)*f x) (hierarchyPairMean_reindex_steps e w φ K [])
  | cons st ss ih =>
    funext x
    change (st.1-a)*hierarchyPairMean w (reindexFeature e φ) K
        (affineSteps (reindexSignedSteps e (st::ss)) t) x+
      varianceTest st.1 (gaussianHierarchy w (reindexFeature e φ) (affineSteps (reindexSignedSteps e ss) t))
        (pathKernelPenalty w (reindexFeature e φ)
          (fun σ τ => K σ τ+featureKernel (reindexFeature e φ) (fun i => st.2.2 (e i)) σ τ)
          st.1 (reindexSignedSteps e ss) t)
        (fun i => st.2.1 (e i)+t*st.2.2 (e i)) x = _
    rw [affineSteps_reindex,affineSteps_reindex,hierarchyPairMean_reindex_steps,
      gaussianHierarchy_reindex_steps,featureKernel_reindex,ih]
    change _+shiftedMean _ _ _ _ x = _+shiftedMean _ _ _ _ (coordinateEquiv e x)
    congr 1
    exact shiftedMean_reindex e (fun i => Real.toNNReal (st.2.1 i+t*st.2.2 i)) st.1 _ _ x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_corrected_affine_variation_finite {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (T : (ι → ℝ) → ℝ)
    (ss : List (SignedStep ι)) (q d : ι → ℝ) {l r : ℝ}
    (hQ : ∀ st ∈ ss, ∀ σ, ∑ i, st.2.2 i*(φ σ (Pi.single i 1))^2 = T st.2.2)
    (hD : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = T d)
    (ha : OrderedSteps 0 (affineSteps ss 0))
    (hq : ∀ st ∈ ss, ∀ t ∈ Ioo l r, ∀ i, 0 < st.2.1 i+t*st.2.2 i)
    {t : ℝ} (ht : t ∈ Ioo l r) (hqt : ∀ i, 0 < q i+t*d i) (x : ι → ℝ) :
    HasDerivAt (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+s*d i))) (gaussianHierarchy w φ (affineSteps ss s)) x-
          (T d+(ss.map fun st => T st.2.2).sum)*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0
        (Real.toNNReal (q i+t*d i)))
        (pathKernelPenalty w φ (featureKernel φ d) 0 ss t) x) t := by
  classical
  let k := Fintype.card ι-1
  have hk : k+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (k+1) ≃ ι := (finCongr hk).trans (Fintype.equivFin ι).symm
  let T' : (Fin (k+1) → ℝ) → ℝ := fun v => T (fun i => v (e.symm i))
  have hp (σ : S) (i : Fin (k+1)) : reindexFeature e φ σ (Pi.single i 1) =
      φ σ (Pi.single (e i) 1) := by
    change φ σ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  have hQ' : ∀ st ∈ reindexSignedSteps e ss, ∀ σ,
      ∑ i, st.2.2 i*(reindexFeature e φ σ (Pi.single i 1))^2 = T' st.2.2 := by
    intro st hs σ
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    dsimp only
    simp_rw [hp]
    rw [e.sum_comp (fun i => z.2.2 i*(φ σ (Pi.single i 1))^2)]
    simpa only [T',e.apply_symm_apply] using hQ z hz σ
  have hD' (σ : S) : ∑ i, d (e i)*(reindexFeature e φ σ (Pi.single i 1))^2 =
      T' (fun i => d (e i)) := by
    simp_rw [hp]
    rw [e.sum_comp (fun i => d i*(φ σ (Pi.single i 1))^2)]
    simpa only [T',e.apply_symm_apply] using hD σ
  have ha' : OrderedSteps 0 (affineSteps (reindexSignedSteps e ss) 0) := by
    rw [affineSteps_reindex]
    exact reindexSteps_ordered e ha
  have hq' : ∀ st ∈ reindexSignedSteps e ss, ∀ s ∈ Ioo l r, ∀ i,
      0 < st.2.1 i+s*st.2.2 i := by
    intro st hs s ht i
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact hq z hz s ht (e i)
  have hd := rootedHierarchy_corrected_affine_variation hw (reindexFeature e φ)
    (fun st => T' st.2.2) (reindexSignedSteps e ss) (fun i => q (e i)) (fun i => d (e i))
    hQ' hD' ha' hq' ht (fun i => hqt (e i)) ((coordinateEquiv e).symm x)
  have hsum : ((reindexSignedSteps e ss).map fun st => T' st.2.2).sum =
      (ss.map fun st => T st.2.2).sum := by
    simp only [reindexSignedSteps,List.map_map,Function.comp_def,T',e.apply_symm_apply]
  rw [hsum,featureKernel_reindex,pathKernelPenalty_reindex] at hd
  simp only [affineSteps_reindex,gaussianHierarchy_reindex_steps] at hd
  have hforce (s : ℝ) : zeroContinuation (Measure.pi fun i => gaussianReal 0
      (Real.toNNReal (q (e i)+s*d (e i))))
      (fun y => gaussianHierarchy w φ (affineSteps ss s) (coordinateEquiv e y)) ((coordinateEquiv e).symm x) =
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+s*d i)))
        (gaussianHierarchy w φ (affineSteps ss s)) x := by
    rw [zeroContinuation_reindex e (fun i => Real.toNNReal (q i+s*d i)),ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [hforce] at hd
  rw [zeroContinuation_reindex e (fun i => Real.toNNReal (q i+t*d i)),
    ContinuousLinearEquiv.apply_symm_apply] at hd
  simpa only [T',e.apply_symm_apply] using hd

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 
def affineCumulative (q r : ℕ → ι → ℝ) (t : ℝ) (j : ℕ) (i : ι) : ℝ :=
  q j i+t*(r j i-q j i)

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem signedClockSteps_at (as : List PositiveMass) (q r : ℕ → ι → ℝ) (t : ℝ) :
    affineSteps (signedClockSteps as q r) t = diagonalBoundarySteps as
      (affineCumulative q r t 0) (fun j => affineCumulative q r t (j+1)) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [signedClockSteps,affineSteps_cons,diagonalBoundarySteps,ih]
    congr 2
    funext i
    congr 1
    simp only [affineCumulative,Pi.sub_apply]
    ring

 

theorem disorderPressure_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (q r : ℕ → ι → ℝ)
    {l u t : ℝ} (ht : t ∈ Ioo l u)
    (hq : ∀ st ∈ signedClockSteps as q r, ∀ s ∈ Ioo l u, ∀ i,
      0 < st.2.1 i+s*st.2.2 i)
    (hq₀ : ∀ i, 0 < affineCumulative q r t 0 i) :
    HasDerivAt (fun s => disorderPressure w φ C as 0 (affineCumulative q r s) 0)
      (-(1/2:ℝ)*massStepSum as 0 (fun j => rootLevelPairMean w φ
        (fun i => Real.toNNReal (affineCumulative q r t 0 i))
        (featureKernel φ (r j-q j)) (affineSteps (signedClockSteps as q r) t) j)) t := by
  let T : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, v i*C i
      map_add' := by intro v z; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a v; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum,RingHom.id_apply] }
  have hT (v : ι → ℝ) (σ : S) : ∑ i, v i*(φ σ (Pi.single i 1))^2 = T v := by
    simp only [hself,T,LinearMap.coe_mk,AddHom.coe_mk]
  have hao : OrderedSteps 0 (affineSteps (signedClockSteps as q r) 0) := by
    rw [affineSteps_signedClock_eq]
    exact clockSteps_ordered ha _
  have hd := rootedHierarchy_corrected_affine_variation_finite hw φ T (signedClockSteps as q r)
    (q 0) (r 0-q 0) (fun st _ => hT st.2.2) (hT (r 0-q 0)) hao hq ht hq₀ (0 : ι → ℝ)
  rw [signedClockSteps_trace] at hd
  simp only [Pi.sub_apply] at hd
  rw [root_pathKernelPenalty_eq_massStepSum hw φ as ha] at hd
  have hc := hd.sub_const (T (q as.length)/2)
  apply hc.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro s
  unfold disorderPressure
  simp only [Pi.zero_apply,sub_zero,← signedClockSteps_at]
  change _ = _ - T (r as.length-q as.length)*s/2-T (q as.length)/2
  have he : (∑ i, affineCumulative q r s as.length i*C i) =
      T (q as.length)+s*T (r as.length-q as.length) := by
    simp only [T,LinearMap.coe_mk,AddHom.coe_mk,affineCumulative,Pi.sub_apply,
      add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  simp only [affineCumulative]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem levelPairMean_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K L : S → S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (c d : ℝ) (j : ℕ) (x : ι → ℝ) :
    levelPairMean w φ (fun σ τ => c*K σ τ+d*L σ τ) steps j x =
      c*levelPairMean w φ K steps j x+d*levelPairMean w φ L steps j x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_linear w φ K L [] c d x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_linear w φ K L _ c d x
    | succ j =>
      change shiftedMean _ st.1 _ (levelPairMean w φ (fun σ τ => c*K σ τ+d*L σ τ) steps j) x = _
      rw [funext (ih ha.2.2.2 j),shiftedMean_add
        ((levelPairMean_smooth hw φ K steps ha.2.2.2 j 0).const_mul c)
        ((levelPairMean_smooth hw φ L steps ha.2.2.2 j 0).const_mul d)
        (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x),
        shiftedMean_const_mul,shiftedMean_const_mul]
      rfl

theorem rootLevelPairMean_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (K L : S → S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (c d : ℝ) (j : ℕ) :
    rootLevelPairMean w φ q (fun σ τ => c*K σ τ+d*L σ τ) steps j =
      c*rootLevelPairMean w φ q K steps j+d*rootLevelPairMean w φ q L steps j := by
  unfold rootLevelPairMean zeroContinuation
  simp_rw [levelPairMean_linear hw φ K L steps ha c d]
  rw [integral_add (((levelPairMean_smooth hw φ K steps ha j 0).integrable_zero_shift 0).const_mul c)
    (((levelPairMean_smooth hw φ L steps ha j 0).integrable_zero_shift 0).const_mul d),
    integral_const_mul,integral_const_mul]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open scoped BigOperators

theorem massStepSum_linear (as : List PositiveMass) (a c d : ℝ) (K L : ℕ → ℝ) :
    massStepSum as a (fun j => c*K j+d*L j) =
      c*massStepSum as a K+d*massStepSum as a L := by
  induction as generalizing a K L with
  | nil => simp only [massStepSum]; ring
  | cons b as ih => simp only [massStepSum,ih]; ring

theorem massStepSum_const (as : List PositiveMass) (a c : ℝ) :
    massStepSum as a (fun _ => c) = (1-a)*c := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => simp only [massStepSum,ih]; ring

theorem massStepSum_mono (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    {K L : ℕ → ℝ} (hKL : ∀ j, j ≤ as.length → K j ≤ L j) :
    massStepSum as a K ≤ massStepSum as a L := by
  induction as generalizing a K L with
  | nil => exact mul_le_mul_of_nonneg_left (hKL 0 le_rfl) (sub_nonneg.mpr ha.2)
  | cons b as ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (hKL 0 (Nat.zero_le _)) (sub_nonneg.mpr ha.2.1))
      (ih ha.2.2 (fun j hj => hKL (j+1) (Nat.succ_le_succ hj)))

theorem massStepSum_nonneg (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    {K : ℕ → ℝ} (hK : ∀ j, j ≤ as.length → 0 ≤ K j) :
    0 ≤ massStepSum as a K := by
  have h := massStepSum_mono as ha hK
  simpa only [massStepSum_const,mul_zero] using h

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

noncomputable def orderedPrefixPair (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ)
    (K : Spin n → Spin n → ℝ) (j : ℕ) : ℝ :=
  rootLevelPairMean (uniformWeight n) (orderedFeature n)
    (fun i => Real.toNNReal (orderedClock n b h 0 i)) K
    (diagonalBoundarySteps as (orderedClock n b h 0) (fun k => orderedClock n b h (k+1))) j

noncomputable def orderedPrefixS (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  orderedPrefixPair n as b h (orderedOverlap n) j

noncomputable def orderedPrefixB (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ) (j : ℕ) : ℝ :=
  orderedPrefixPair n as b h (fun σ τ => (orderedOverlap n σ τ)^2) j

theorem affine_orderedClock (n : ℕ) (b h b' h' : ℕ → ℝ) (t : ℝ) :
    affineCumulative (orderedClock n b h) (orderedClock n b' h') t =
      orderedClock n (fun j => b j+t*(b' j-b j)) (fun j => h j+t*(h' j-h j)) := by
  funext j i
  cases i <;> rfl

 

theorem orderedSKPressure_hasDerivAt (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ha : MassOrdered 0 as) (b h b' h' : ℕ → ℝ) {l u t : ℝ} (ht : t ∈ Ioo l u)
    (hq : ∀ st ∈ signedClockSteps as (orderedClock n b h) (orderedClock n b' h'),
      ∀ s ∈ Ioo l u, ∀ i, 0 < st.2.1 i+s*st.2.2 i)
    (hq₀ : ∀ i, 0 < affineCumulative (orderedClock n b h) (orderedClock n b' h') t 0 i) :
    HasDerivAt (fun s => orderedSKPressure n as
      (fun j => b j+s*(b' j-b j)) (fun j => h j+s*(h' j-h j)) 0)
      (-(1/4:ℝ)*massStepSum as 0 (fun j => (b' j-b j)*orderedPrefixB n as
        (fun k => b k+t*(b' k-b k)) (fun k => h k+t*(h' k-h k)) j)-
       (1/2:ℝ)*massStepSum as 0 (fun j => (h' j-h j)*orderedPrefixS n as
        (fun k => b k+t*(b' k-b k)) (fun k => h k+t*(h' k-h k)) j)) t := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let q := orderedClock n b h
  let r := orderedClock n b' h'
  let qt := affineCumulative q r t
  let sts := affineSteps (signedClockSteps as q r) t
  have ho : OrderedSteps 0 sts := by
    dsimp [sts]
    rw [affineSteps_signedClock_eq]
    exact clockSteps_ordered ha _
  have hk (j : ℕ) : featureKernel (orderedFeature n) (r j-q j) =
      fun σ τ => ((n:ℝ)/2)*((b' j-b j)*(orderedOverlap n σ τ)^2)+
        (n:ℝ)*((h' j-h j)*orderedOverlap n σ τ) := by
    funext σ τ
    have he : r j-q j = Sum.elim (fun _ => h' j-h j) (fun _ => b' j-b j) := by
      funext i; cases i <;> rfl
    rw [he]
    simp only [featureKernel,orderedFeature_single]
    rw [orderedCovariance n hn]
    ring
  have hm (j : ℕ) : rootLevelPairMean (uniformWeight n) (orderedFeature n)
      (fun i => Real.toNNReal (qt 0 i)) (featureKernel (orderedFeature n) (r j-q j)) sts j =
      (n:ℝ)/2*((b' j-b j)*orderedPrefixB n as
        (fun k => b k+t*(b' k-b k)) (fun k => h k+t*(h' k-h k)) j)+
      (n:ℝ)*((h' j-h j)*orderedPrefixS n as
        (fun k => b k+t*(b' k-b k)) (fun k => h k+t*(h' k-h k)) j) := by
    rw [hk]
    have he : (fun σ τ => (n:ℝ)/2*((b' j-b j)*(orderedOverlap n σ τ)^2)+
        (n:ℝ)*((h' j-h j)*orderedOverlap n σ τ)) =
        fun σ τ => ((n:ℝ)/2*(b' j-b j))*(orderedOverlap n σ τ)^2+
          ((n:ℝ)*(h' j-h j))*orderedOverlap n σ τ := by funext σ τ; ring
    rw [he,rootLevelPairMean_linear (uniformWeight_pos n) (orderedFeature n) _ _ _ sts ho]
    dsimp [orderedPrefixB,orderedPrefixS,orderedPrefixPair,qt,sts,q,r]
    rw [signedClockSteps_at,affine_orderedClock]
    ring
  have hd := (disorderPressure_hasDerivAt (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedFeature_square n)
    as ha q r ht hq hq₀).div_const (n:ℝ)
  change HasDerivAt (fun s => disorderPressure (uniformWeight n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) as 0 (affineCumulative q r s) 0/(n:ℝ))
    ((-(1/2:ℝ)*massStepSum as 0 (fun j => rootLevelPairMean (uniformWeight n) (orderedFeature n)
      (fun i => Real.toNNReal (qt 0 i)) (featureKernel (orderedFeature n) (r j-q j)) sts j))/(n:ℝ)) t at hd
  simp_rw [hm] at hd
  rw [massStepSum_linear] at hd
  have he : (fun s => disorderPressure (uniformWeight n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) as 0 (affineCumulative q r s) 0/(n:ℝ)) =
      fun s => orderedSKPressure n as (fun j => b j+s*(b' j-b j))
        (fun j => h j+s*(h' j-h j)) 0 := by
    funext s
    dsimp [q,r]
    rw [affine_orderedClock]
    rfl
  rw [he] at hd
  convert hd using 1
  field_simp
  ring

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem orderedPrefix_bounds (n : ℕ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b h : ℕ → ℝ) (j : ℕ) :
    0 ≤ orderedPrefixS n as b h j ∧ orderedPrefixS n as b h j ≤ 1 ∧
    (orderedPrefixS n as b h j)^2 ≤ orderedPrefixB n as b h j ∧ orderedPrefixB n as b h j ≤ 1 := by
  have ho : OrderedSteps 0 (diagonalBoundarySteps as (orderedClock n b h 0)
      (fun k => orderedClock n b h (k+1))) := by
    have hh : OrderedSteps 0 (affineSteps
        (signedClockSteps as (orderedClock n b h) (orderedClock n b h)) 0) := by
      rw [affineSteps_signedClock_eq]
      exact clockSteps_ordered ha _
    rw [signedClockSteps_at] at hh
    have he : affineCumulative (orderedClock n b h) (orderedClock n b h) 0 = orderedClock n b h := by
      funext k i
      simp only [affineCumulative,zero_mul,add_zero]
    rw [he] at hh
    exact hh
  exact rootLevelPairMean_SK_bounds n (uniformWeight_pos n) (orderedFeature n) _ _ ho j

 
noncomputable def orderedCompensatedSquare (n : ℕ) (as : List PositiveMass) (b h r : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  orderedPrefixB n as b h j-(orderedPrefixS n as b h j)^2+
    (orderedPrefixS n as b h j-r j)^2

theorem orderedCompensatedSquare_nonneg (n : ℕ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b h r : ℕ → ℝ) (j : ℕ) : 0 ≤ orderedCompensatedSquare n as b h r j :=
  add_nonneg (sub_nonneg.mpr (orderedPrefix_bounds n as ha b h j).2.2.1) (sq_nonneg _)

theorem orderedCompensatedSquare_le (n : ℕ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b h r : ℕ → ℝ) (j : ℕ) (hr : r j ∈ Icc (0:ℝ) 1) :
    orderedCompensatedSquare n as b h r j ≤ 2 := by
  have hb := orderedPrefix_bounds n as ha b h j
  unfold orderedCompensatedSquare
  have hb1 := hb.2.2.2
  nlinarith [mul_nonneg hr.1 hb.1,mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]

 

noncomputable def finiteCompensatedSweep (n : ℕ) (as : List PositiveMass)
    (b h e r : ℕ → ℝ) (t : ℝ) : ℝ :=
  orderedSKPressure n as (fun j => b j-t*e j) (fun j => h j+t*e j*r j) 0+
    t/4*massStepSum as 0 (fun j => e j*(r j)^2)

theorem massStepSum_compensated (as : List PositiveMass) (a : ℝ) (e r B S : ℕ → ℝ) :
    (1/4:ℝ)*massStepSum as a (fun j => e j*(B j-(S j)^2+(S j-r j)^2)) =
      (1/4:ℝ)*massStepSum as a (fun j => e j*B j)-
      (1/2:ℝ)*massStepSum as a (fun j => (e j*r j)*S j)+
      (1/4:ℝ)*massStepSum as a (fun j => e j*(r j)^2) := by
  have he : (fun j => e j*(B j-(S j)^2+(S j-r j)^2)) =
      fun j => 1*(1*(e j*B j)+(-2)*((e j*r j)*S j))+1*(e j*(r j)^2) := by funext j; ring
  rw [he,massStepSum_linear,massStepSum_linear]
  ring

theorem finiteCompensatedSweep_hasDerivAt (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ha : MassOrdered 0 as) (b h e r : ℕ → ℝ) {l u t : ℝ} (ht : t ∈ Ioo l u)
    (hq : ∀ st ∈ signedClockSteps as (orderedClock n b h)
      (orderedClock n (fun j => b j-e j) (fun j => h j+e j*r j)),
      ∀ s ∈ Ioo l u, ∀ i, 0 < st.2.1 i+s*st.2.2 i)
    (hq₀ : ∀ i, 0 < affineCumulative (orderedClock n b h)
      (orderedClock n (fun j => b j-e j) (fun j => h j+e j*r j)) t 0 i) :
    HasDerivAt (finiteCompensatedSweep n as b h e r)
      ((1/4:ℝ)*massStepSum as 0 (fun j => e j*orderedCompensatedSquare n as
        (fun k => b k-t*e k) (fun k => h k+t*e k*r k) r j)) t := by
  have hd := orderedSKPressure_hasDerivAt n hn as ha b h (fun j => b j-e j)
    (fun j => h j+e j*r j) ht hq hq₀
  have hb (s : ℝ) : (fun j => b j+s*(b j-e j-b j)) = fun j => b j-s*e j := by funext j; ring
  have hh (s : ℝ) : (fun j => h j+s*(h j+e j*r j-h j)) = fun j => h j+s*e j*r j := by funext j; ring
  simp_rw [hb,hh] at hd
  have hp := hd.add ((hasDerivAt_id t).mul_const ((1/4:ℝ)*massStepSum as 0 (fun j => e j*(r j)^2)))
  have he : (fun x => orderedSKPressure n as (fun j => b j-x*e j) (fun j => h j+x*e j*r j) 0+
      x*((1/4:ℝ)*massStepSum as 0 (fun j => e j*(r j)^2))) = finiteCompensatedSweep n as b h e r := by
    funext x
    unfold finiteCompensatedSweep
    ring
  simp only [Pi.add_def,id_eq] at hp
  rw [he] at hp
  convert! hp using 1
  unfold orderedCompensatedSquare
  rw [massStepSum_compensated]
  have hz : (fun j => (b j-e j-b j)*orderedPrefixB n as
      (fun k => b k-t*e k) (fun k => h k+t*e k*r k) j) =
      fun j => (-1)*(e j*orderedPrefixB n as
        (fun k => b k-t*e k) (fun k => h k+t*e k*r k) j)+0*0 := by funext j; ring
  rw [hz,massStepSum_linear]
  simp only [add_sub_cancel_left,zero_mul,add_zero,one_mul]
  ring

 

theorem compensatedRate_bounds (n : ℕ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (b h e r : ℕ → ℝ) (he : ∀ j, j ≤ as.length → 0 ≤ e j)
    (hr : ∀ j, j ≤ as.length → r j ∈ Icc (0:ℝ) 1) :
    0 ≤ (1/4:ℝ)*massStepSum as 0 (fun j => e j*orderedCompensatedSquare n as b h r j) ∧
    (1/4:ℝ)*massStepSum as 0 (fun j => e j*orderedCompensatedSquare n as b h r j) ≤
      (1/2:ℝ)*massStepSum as 0 e := by
  constructor
  · exact mul_nonneg (by norm_num) (massStepSum_nonneg as ha
      (fun j hj => mul_nonneg (he j hj) (orderedCompensatedSquare_nonneg n as ha b h r j)))
  · have hb := massStepSum_mono as ha (fun j hj => mul_le_mul_of_nonneg_left
      (orderedCompensatedSquare_le n as ha b h r j (hr j hj)) (he j hj))
    have hz : (fun j => e j*2) = fun j => 2*e j+0*0 := by funext j; ring
    rw [hz,massStepSum_linear] at hb
    simp only [zero_mul,add_zero] at hb
    linarith

end SKFluctuations

end

end OAI
