import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ComplexMul
import OAI.Geometry.SmoothYau.Estimates.ExistsAnnularSimplePinnedFamily
import OAI.Geometry.SmoothYau.Smoothness.ChartTensorCoordLocal1

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {P E M : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
local instance persistence_smulComm (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul,mul_comm]⟩
local instance persistence_scalarTower (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩

theorem actual_simple_eigenpair_persistence
    (I : MetricIntegralAtlas (E:=E) (M:=M))
    (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α*(A.localInverse i).radius^2) (he : A.errorBound B α ≤ 1/2)
    (lam : ℝ) (hn : α+lam ≠ 0)
    (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami g u x = lam*u x)
    (hsimple : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami g v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (q : P → SmoothMetric E M) (p₀ : P) (hq0 : q p₀ = g)
    (hq : ∀ i j l, ContinuousSmoothFamilyOn
      (fun t y => metricCoefficients (q t) (A.p i) y j l) (chartAt E (A.p i)).target) :
    ∃ (e : P → ℝ) (w : P → A.realH (2*((k+1:ℕ):ℝ))),
      e p₀ = lam ∧ A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) = u ∧
      ContinuousAt e p₀ ∧ ContinuousAt w p₀ ∧
      ∀ᶠ p in 𝓝 p₀,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) ∧
        A.realValue (2*((k+1:ℕ):ℝ)) (w p) ≠ 0 ∧
        ∀ x, -laplaceBeltrami (q p) (A.realValue (2*((k+1:ℕ):ℝ)) (w p)) x =
          e p*A.realValue (2*((k+1:ℕ):ℝ)) (w p) x := by
  classical
  let C : ∀ p i, A.VaryingPatchCoefficients (q p) i := fun p i =>
    (A.nonempty_varyingPatchCoefficients (q p) i).some
  let C₀ : ∀ i, A.VaryingPatchCoefficients g i := hq0 ▸ C p₀
  have hc := A.continuousFamily_varyingLaplacian_tendsto q hq C p₀
  have hbase : A.varyingLaplacianCLM (q p₀) (C p₀) = A.varyingLaplacianCLM g C₀ := by
    subst g
    rfl
  rw [hbase] at hc
  obtain ⟨hunit,hRlim⟩ := A.varyingResolvent_tendsto B α hα0 hα he C₀ q C
    (A.varyingShift_tendsto q g C C₀ α hc)
  let R (p : P) := A.varyingResolvent B α hα0 hα he (q p) (C p)
  let R₀ := A.realResolvent B α hα0 hα he
  let T (p : P) := A.realInclusion ∘L R p
  let T₀ := A.realSpectralResolvent B α hα0 hα he
  have hR0 : R p₀ = R₀ := by
    dsimp only [R,R₀]
    subst g
    exact A.varyingResolvent_base B α hα0 hα he (C p₀)
  have hT0 : T p₀ = T₀ := congrArg (fun R => A.realInclusion ∘L R) hR0
  have hcomp : Continuous (fun R : A.realH (2*(k:ℝ)) →L[ℝ] A.realH (2*((k+1:ℕ):ℝ)) =>
      A.realInclusion ∘L R) := by fun_prop
  have hTlim : Tendsto T (𝓝 p₀) (𝓝 T₀) := hcomp.tendsto R₀ |>.comp hRlim
  let μ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hn
  have hμv : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let uz := A.realOfSmooth (2*(k:ℝ)) hs u hu
  have huz : uz ≠ 0 := by
    intro hz
    apply hu0
    funext x
    have hh := congrArg (fun z => A.realValue (2*(k:ℝ)) z x) hz
    have hzv : A.realValue (2*(k:ℝ)) 0 x = 0 := by
      simpa only [zero_smul,zero_mul] using A.realValue_smul (2*(k:ℝ)) 0 uz x
    simpa only [uz,A.realOfSmooth_value,hzv,Pi.zero_apply] using hh
  have hueT : T₀ uz = μ • uz := A.shiftedInverse_of_smooth_eigenfunction g α hα0 R₀
    (A.realResolvent_value B α hα0 hα he) lam hn u hu hue
  have hsimpleT : ∀ z, T₀ z = μ • z → ∃ c : ℝ, z = c • uz := by
    intro z hz
    obtain ⟨hzs,hze⟩ := A.realSpectralResolvent_eigenfunction B α hα0 hα he hμ z hz
    rw [hμv] at hze
    obtain ⟨c,hc⟩ := hsimple _ hzs hze
    refine ⟨c,?_⟩
    apply A.realRepresentative_injective (2*(k:ℝ)) hs
    ext x
    change A.realValue _ z x = A.realValue _ (c • uz) x
    rw [A.realValue_smul,A.realOfSmooth_value]
    exact congrFun hc x
  obtain ⟨ev,v,hev,hv,hcev,hcv,hpair⟩ := (A.intrinsicPairing I (2*(k:ℝ)) hs).simple_eigenpair_persistence
    T₀ (A.realSpectralResolvent_compact B α hα0 hα he)
    (A.realSpectralResolvent_symmetric I B α hα0 hα he) hμ huz hueT hsimpleT
  let e (p : P) := (ev (T p))⁻¹-α
  let w (p : P) := (ev (T p))⁻¹ • R p (v (T p))
  have heT : Tendsto (fun p => ev (T p)) (𝓝 p₀) (𝓝 μ) := hev ▸ hcev.tendsto.comp hTlim
  have hvT : Tendsto (fun p => v (T p)) (𝓝 p₀) (𝓝 uz) := hv ▸ hcv.tendsto.comp hTlim
  have hinv : Tendsto (fun p => (ev (T p))⁻¹) (𝓝 p₀) (𝓝 μ⁻¹) := heT.inv₀ hμ
  have hev0 : ev (T p₀) = μ := hT0 ▸ hev
  have hv0 : v (T p₀) = uz := hT0 ▸ hv
  have hw0 (x : M) : A.realValue (2*((k+1:ℕ):ℝ)) (w p₀) x = u x := by
    dsimp only [w]
    rw [hev0,hv0,hR0,A.realValue_smul,← A.realValue_inclusion]
    change μ⁻¹*A.realValue (2*(k:ℝ)) (T₀ uz) x = u x
    rw [hueT,A.realValue_smul,A.realOfSmooth_value,← mul_assoc,inv_mul_cancel₀ hμ,one_mul]
  refine ⟨e,w,by simpa only [e,hev0] using hμv,funext hw0,?_,?_,?_⟩
  · change Tendsto e (𝓝 p₀) (𝓝 (e p₀))
    simpa only [e,hev0] using hinv.sub_const α
  · have happly := (isBoundedBilinearMap_apply (𝕜:=ℝ)
      (E:=A.realH (2*(k:ℝ))) (F:=A.realH (2*((k+1:ℕ):ℝ)))).continuous.tendsto (R₀,uz)
    have hwlim := hinv.smul (happly.comp (hRlim.prodMk_nhds hvT))
    change Tendsto w (𝓝 p₀) (𝓝 (w p₀))
    simpa only [w,hev0,hv0,hR0,Function.comp_apply,R] using hwlim
  · have hne : ∀ᶠ p in 𝓝 p₀, ev (T p) ≠ 0 := heT.eventually (isOpen_ne.mem_nhds hμ)
    filter_upwards [hunit,hTlim.eventually hpair,hne] with p hp hpv hpev
    have hshift := A.varyingResolvent_equation B α hα0 hα he (q p) (C p) hp
    obtain ⟨hsm,heig⟩ := A.shiftedInverse_eigenfunction (q p) α (R p) hshift hpev (v (T p)) hpv.2.1
    have hval : A.realValue (2*((k+1:ℕ):ℝ)) (w p) = A.realValue (2*(k:ℝ)) (v (T p)) := by
      funext x
      rw [show w p = (ev (T p))⁻¹ • R p (v (T p)) from rfl,A.realValue_smul,
        ← A.realValue_inclusion]
      change (ev (T p))⁻¹*A.realValue (2*(k:ℝ)) (T p (v (T p))) x = _
      rw [hpv.2.1,A.realValue_smul,← mul_assoc,inv_mul_cancel₀ hpev,one_mul]
    rw [hval]
    refine ⟨hsm,?_,heig⟩
    intro hz
    apply hpv.1
    apply A.realRepresentative_injective (2*(k:ℝ)) hs
    ext x
    change A.realValue _ (v (T p)) x = A.realValue _ 0 x
    rw [hz]
    simpa only [zero_smul,zero_mul,Pi.zero_apply] using
      (A.realValue_smul (2*(k:ℝ)) 0 (v (T p)) x).symm
end CompactMetricAtlas
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff BoundedContinuousFunction ENNReal NNReal
variable {P : Type*} [TopologicalSpace P]
lemma spherical_simple_eigenpair_open (q : P → SmoothMetric (Euclidean 3) (Sphere 3))
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt (Euclidean 3) r).target) (a₀ : P)
    (lam : ℝ) (hlam : 0 < lam) (u : Sphere 3 → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x = lam*u x)
    (hsimple : ∀ v, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
      (∀ x, -laplaceBeltrami (q a₀) v x = lam*v x) → ∃ c : ℝ, v = fun x => c*u x)
    (hreg : ∀ x, u x=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) x).symm)
      ((chartAt (Euclidean 3) x) x) ≠ 0)
    {J : Type*} [Fintype J] (Q : J → Set (Fin 3 → ℝ)) (d : J → ℝ)
    (ψ : (Fin 3 → ℝ) → Sphere 3) (hψ : Continuous ψ)
    (L : ℝ≥0∞) (hL : L < SignTests.signCertificate Q d (u ∘ ψ))
    {B D : ℝ} (hB : B < lam) (hD : lam < D) :
    ∀ᶠ a in 𝓝 a₀, ∃ e : ℝ, ∃ v : Sphere 3 → ℝ,
      B < e ∧ e < D ∧ ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ x, -laplaceBeltrami (q a) v x = e*v x) ∧
      (∀ x, v x=0 → fderiv ℝ (v ∘ (chartAt (Euclidean 3) x).symm)
        ((chartAt (Euclidean 3) x) x) ≠ 0) ∧
      L < SignTests.signCertificate Q d (v ∘ ψ) := by
  classical
  have hs : Module.finrank ℝ (Euclidean 3) < 2*(2*(2:ℝ)) := by norm_num [Euclidean]
  let A := (nonempty_compactMetricAtlas (q a₀) 2 hs).some
  let I := (nonempty_metricIntegralAtlas (E:=Euclidean 3) (M:=Sphere 3)).some
  let C : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold C
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  obtain ⟨e,w,he,hw,hce,hcw,hpair⟩ := A.actual_simple_eigenpair_persistence I C α hα0
    (hα α le_rfl).1 (hα α le_rfl).2 lam (ne_of_gt (add_pos hα0 hlam))
    u hu hu0 hue hsimple q a₀ rfl (fun i => hq (A.p i))
  have hwr : ∀ᶠ a in 𝓝 a₀, ∀ x, A.realValue A.highIndex (w a) x=0 →
      fderiv ℝ (A.realValue A.highIndex (w a) ∘ (chartAt (Euclidean 3) x).symm)
        ((chartAt (Euclidean 3) x) x) ≠ 0 :=
    hcw.eventually (A.eventually_regular_realValue (w a₀) (by simpa only [hw] using hreg))
  let f (v : A.realH A.highIndex) : (Fin 3 → ℝ) → ℝ := A.realValue A.highIndex v ∘ ψ
  have hf : LowerSemicontinuous (fun v => SignTests.signCertificate Q d (f v)) := by
    apply SignTests.lowerSemicontinuous_signCertificate
    · intro v
      exact ((A.realRepresentative A.highIndex v).continuous.comp hψ).measurable
    · intro y
      exact (A.realRepresentative A.highIndex).continuous.eval_const (ψ y)
  have hwl : ∀ᶠ a in 𝓝 a₀, L < SignTests.signCertificate Q d (f (w a)) :=
    hcw.eventually (hf (w a₀) L (by simpa only [f,hw] using hL))
  have heb : ∀ᶠ a in 𝓝 a₀, B < e a := hce.eventually (lt_mem_nhds (he ▸ hB))
  have hed : ∀ᶠ a in 𝓝 a₀, e a < D := hce.eventually (gt_mem_nhds (he ▸ hD))
  filter_upwards [hpair,hwr,hwl,heb,hed] with a ha hr hl hb hd
  exact ⟨e a,A.realValue A.highIndex (w a),hb,hd,ha.1,ha.2.1,ha.2.2,hr,hl⟩

end YauCounterexamples
end

end OAI
