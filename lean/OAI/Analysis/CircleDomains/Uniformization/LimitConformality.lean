import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension

namespace OAI

/-!
# Conformality of the normalized limit

`HurwitzZeroFreeLimit` records the zero-free form of the same published
Hurwitz theorem already used for injective limits: Ahlfors, *Complex
Analysis*, third edition (1979), Chapter 5, Theorem 2, p. 178. Applied
to the derivatives, it gives a nonzero limiting derivative unless the
limit is constant. The latter alternative is ruled out on each core.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def HurwitzZeroFreeLimit : Prop :=
  ∀ (D : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsOpen D → IsConnected D →
    (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, F n z ≠ 0) →
    TendstoLocallyUniformlyOn F f atTop D →
    (∀ z ∈ D, f z = 0) ∨ (∀ z ∈ D, f z ≠ 0)

theorem finite_part_deriv_ne_zero
    {f : Sphere → Sphere} {z : ℂ}
    (hf : IsConformalAt f (z : Sphere)) (hfinite : f (z : Sphere) ≠ OnePoint.infty) :
    deriv (fun w : ℂ => finiteCoord (f (w : Sphere))) z ≠ 0 := by
  obtain ⟨_, d, hd, hder⟩ := hf
  have he : (fun w => chart (f (z : Sphere)) (f (chartSymm (z : Sphere) w))) =
      (fun w : ℂ => finiteCoord (f (w : Sphere))) := by
    funext w
    simp only [chart, hfinite, ite_false, chartSymm_coe_apply]
  rw [he, chart_coe_self] at hder
  rwa [hder.deriv]

theorem deriv_ne_zero_of_holomorphic_limits
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hnonconst : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) :
    ∀ z ∈ D, deriv f z ≠ 0 := by
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D := hF.mono fun _ h => h.1
  have hderdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (deriv (F n)) D ∧ ∀ z ∈ D, deriv (F n) z ≠ 0 := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1.deriv hD, hn.2⟩
  have hderlim := hlim.deriv hdiff hD
  rcases hhurwitz D (fun n => deriv (F n)) (deriv f) hD hconn hderdiff hderlim with hz | hn
  · exact (hnonconst (hD.exists_is_const_of_deriv_eq_zero hconn.isPreconnected
      (hlim.differentiableOn hdiff hD) (fun z hzD => hz z hzD))).elim
  · exact hn

theorem deriv_ne_zero_on_exhaustion
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFn : ∀ n z, z ∈ D n → deriv (F n) z ≠ 0) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    ∀ z ∈ ⋃ n, D n, deriv f z ≠ 0 := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  apply deriv_ne_zero_of_holomorphic_limits hhurwitz (hD m) (hconn m) ?_
    (hlim.mono (subset_iUnion D m)) (hnonconst m) z hm
  filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
  exact ⟨(hF (s n)).mono (hmono hn), fun w hw => hFn (s n) w (hmono hn hw)⟩

theorem isConformalAt_extendAtInfinity_coe
    {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F z) (hd : deriv F z ≠ 0) :
    IsConformalAt (extendAtInfinity F) (z : Sphere) := by
  refine ⟨OnePoint.continuousAt_coe.mpr ?_, deriv F z, hd, ?_⟩
  · exact OnePoint.continuous_coe.continuousAt.comp hF.continuousAt
  · simpa only [extendAtInfinity_coe, chart_coe_apply, chartSymm_coe_apply,
      chart_coe_self, finiteCoord_coe] using hF.hasDerivAt

theorem isConformalOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hF : DifferentiableOn ℂ F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp)
  · exact isConformalAt_extendAtInfinity_coe
      ((hF z hz).differentiableAt (hD.mem_nhds hz)) (hd z hz)
  · rw [mem_singleton_iff] at hp
    subst p
    exact isConformalAt_extendAtInfinity_infty hnorm

end CircleDomainRigidity

end

end OAI
