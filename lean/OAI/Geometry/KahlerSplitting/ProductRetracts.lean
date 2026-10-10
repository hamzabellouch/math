import OAI.Geometry.KahlerSplitting.SwapSplitting

namespace OAI

section

noncomputable section
open Set unitInterval
namespace UniversalCoverSplitting

lemma simplyConnected_fixed {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    {Q : A → A} (hQc : Continuous Q) (hQ : ∀ a, Q (Q a)=Q a) :
    SimplyConnectedSpace {a : A // Q a=a} := by
  let q : A → {a : A // Q a=a} := fun a ↦ ⟨Q a,hQ a⟩
  have hq : Continuous q := hQc.subtype_mk _
  have hsur : Function.Surjective q := fun a ↦ ⟨a.val,Subtype.ext a.property⟩
  have hpc := hsur.pathConnectedSpace hq
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc,?_⟩
  intro x y p₁ p₂
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
    (p₁.map continuous_subtype_val) (p₂.map continuous_subtype_val)
  refine ⟨{ toFun := fun p ↦ q (H p)
            continuous_toFun := hq.comp H.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    change Q (H (0,t))=(p₁ t).val
    exact (congrArg Q (show H (0,t)=(p₁ t).val from H.map_zero_left t)).trans (p₁ t).property
  · intro t
    apply Subtype.ext
    change Q (H (1,t))=(p₂ t).val
    exact (congrArg Q (show H (1,t)=(p₂ t).val from H.map_one_left t)).trans (p₂ t).property
  · intro t u hu
    apply Subtype.ext
    change Q (H (t,u))=(p₁ u).val
    rw [H.eq_fst t hu]
    exact (p₁ u).property

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma integrable_swap_complement (h₁ : Integrable S.projection) :
    Integrable (complementaryProjection S.swap) := by rwa [complementaryProjection_swap]

structure ProductRetracts (π : OrdinaryUniversalCover X Z) (o : Z.Carrier)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) where
  first : FirstGerm.GlobalProjection π o h₁ h₂
  second : FirstGerm.GlobalProjection π o h₂ (integrable_swap_complement h₁)
  firstCharts : RetractChart.Fixed first.toFun → RetractChart Z first.toFun r s
  first_mem : ∀ x, x.val ∈ (firstCharts x).chart.source
  secondCharts : RetractChart.Fixed second.toFun → RetractChart Z second.toFun s r
  second_mem : ∀ x, x.val ∈ (secondCharts x).chart.source

lemma exists_productRetracts [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (π : OrdinaryUniversalCover X Z) (o : Z.Carrier) :
    Nonempty (ProductRetracts π o h₁ h₂) := by
  classical
  obtain ⟨Q⟩ := FirstGerm.exists_globalProjection g h₁ h₂ π o
  obtain ⟨R⟩ := FirstGerm.exists_globalProjection g h₂ (integrable_swap_complement h₁) π o
  have hc (x : RetractChart.Fixed Q.toFun) := Q.exists_retractChart g x.property
  have hd (x : RetractChart.Fixed R.toFun) := R.exists_retractChart g x.property
  choose c hc₁ hc₂ using hc
  choose d hd₁ hd₂ using hd
  exact ⟨⟨Q,R,c,hc₁,d,hd₁⟩⟩

namespace ProductRetracts
variable (P : ProductRetracts π o h₁ h₂)

def Y₁ : ComplexManifold r := RetractChart.fixedManifold P.firstCharts P.first_mem
def Y₂ : ComplexManifold s := RetractChart.fixedManifold P.secondCharts P.second_mem

variable [CompactSpace X.Carrier] (g : KahlerMetric X)

def q₁ : Z.Carrier → P.Y₁.Carrier := fun z ↦ ⟨P.first.toFun z,P.first.idempotent g z⟩
def q₂ : Z.Carrier → P.Y₂.Carrier := fun z ↦ ⟨P.second.toFun z,P.second.idempotent g z⟩
def pair : Z.Carrier → P.Y₁.Carrier × P.Y₂.Carrier := fun z ↦ (P.q₁ g z,P.q₂ g z)

lemma q₁_holomorphic : MDifferentiable (model n) (model r) (P.q₁ g) :=
  RetractChart.fixed_projection_holomorphic P.firstCharts P.first_mem P.first.holomorphic
    (P.first.idempotent g)
lemma q₂_holomorphic : MDifferentiable (model n) (model s) (P.q₂ g) :=
  RetractChart.fixed_projection_holomorphic P.secondCharts P.second_mem P.second.holomorphic
    (P.second.idempotent g)
lemma pair_holomorphic : MDifferentiable (model n) ((model r).prod (model s)) (P.pair g) :=
  (P.q₁_holomorphic g).prodMk (P.q₂_holomorphic g)

lemma q₁_submersion (z : Z.Carrier) : Function.Surjective (mfderiv (model n) (model r) (P.q₁ g) z) :=
  P.first.submersion g P.firstCharts P.first_mem z
lemma q₂_submersion (z : Z.Carrier) : Function.Surjective (mfderiv (model n) (model s) (P.q₂ g) z) :=
  P.second.submersion g P.secondCharts P.second_mem z

lemma q₁_factor (e : CoverProductChart π S) :
    EqOn (P.q₁ g) (fun w ↦ P.q₁ g (e.chart.symm ((e.chart w).1,0))) e.chart.source := by
  intro w hw
  exact Subtype.ext (P.first.chart_factor e hw)
lemma q₂_factor (e : CoverProductChart π S) :
    EqOn (P.q₂ g) (fun w ↦ P.q₂ g (e.chart.symm (0,(e.chart w).2))) e.chart.source := by
  intro w hw
  exact Subtype.ext (P.second.chart_factor e.swap hw)

include g in
lemma simplyConnected_first : SimplyConnectedSpace P.Y₁.Carrier := by
  let := π.simplyConnected
  exact simplyConnected_fixed P.first.holomorphic.continuous (P.first.idempotent g)
include g in
lemma simplyConnected_second : SimplyConnectedSpace P.Y₂.Carrier := by
  let := π.simplyConnected
  exact simplyConnected_fixed P.second.holomorphic.continuous (P.second.idempotent g)

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold r}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.factor_kernel (e : CoverProductChart π S)
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model r) f)
    (hfact : EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {z : Z.Carrier} (hz : z ∈ e.chart.source)
    (hsur : Function.Surjective (mfderiv (model n) (model r) f z)) (v : Tangent Z z) :
    mfderiv (model n) (model r) f z v=0 ↔
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1=0 := by
  let h : Model r → Y.Carrier := fun a ↦ f (e.chart.symm (a,0))
  let a := (e.chart z).1
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have hta : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ht.1,mem_ball_self e.radius_pos⟩
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hta)
  have hin : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hh : MDifferentiableAt (model r) (model r) h a :=
    (hf (e.chart.symm (a,0))).comp a (hi.comp a hin)
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hfirst : MDifferentiableAt (model n) (model r) (fun w ↦ (e.chart w).1) z :=
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z he
  have H := mfderiv_comp (I := model n) (I' := model r) (I'' := model r) z hh hfirst
  have heq : f =ᶠ[𝓝 z] h ∘ (fun w ↦ (e.chart w).1) := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact hfact hw
  have hderiv : mfderiv (model n) (model r) f z =
      mfderiv (model n) (model r) (h ∘ fun w ↦ (e.chart w).1) z := heq.mfderiv_eq
  rw [←hderiv] at H
  have hhsur := (e.surjective_factor_iff hf hfact hz).mp hsur
  have hhinj : Function.Injective (mfderiv (model r) (model r) h a) :=
    (LinearMap.injective_iff_surjective (f := (show Model r →ₗ[ℂ] Model r from (mfderiv (model r) (model r) h a).toLinearMap))).mpr hhsur
  have Hfirst := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := model r) z (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst) he
  rw [mfderiv_eq_fderiv,hasFDerivAt_fst.fderiv] at Hfirst
  change mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z = _ at Hfirst
  rw [H,Hfirst]
  change mfderiv (model r) (model r) h a ((mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1)=0 ↔ _
  exact map_eq_zero_iff _ hhinj

end UniversalCoverSplitting
end
end

end OAI
