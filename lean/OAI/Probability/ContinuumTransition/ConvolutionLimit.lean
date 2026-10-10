import OAI.Probability.ContinuumTransition.IdealSlopes

namespace OAI

universe u_1 u_2

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma locallyUniform_reindex {ι : Type u_1} {κ : Type u_2} {l : Filter ι} {k : Filter κ}
    {Q : ι → Parameter → ℝ} {q : Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q l pressureDomain)
    {θ : κ → ι} (hθ : Tendsto θ k l) :
    TendstoLocallyUniformlyOn (fun n => Q (θ n)) q k pressureDomain := by
  intro u hu x hx
  obtain ⟨t,ht,h⟩ := hQ u hu x hx
  exact ⟨t,ht,hθ.eventually h⟩

lemma quadraticCost_tendsto {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hq : ContinuousOn q pressureDomain)
    {a d : ℕ → ℝ} {a₀ d₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀))
    (hd : Tendsto d atTop (𝓝 d₀)) {X : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x)) :
    Tendsto (fun n => quadraticCost (Q n) (a n) (X n) (d n)) atTop
      (𝓝 (quadraticCost q a₀ x d₀)) := by
  have hX1 := (continuous_fst.tendsto x).comp hX
  have hX2 := (continuous_snd.tendsto x).comp hX
  have hf : Tendsto (fun n => shiftedField (a n) (X n) (d n)) atTop
      (𝓝 (shiftedField a₀ x d₀)) :=
    hX1.prodMk_nhds (hX2.add ((hX1.mul ha).mul hd))
  have he : ∀ᶠ n in atTop, shiftedField (a n) (X n) (d n) ∈ pressureDomain :=
    (hX.eventually (isOpen_pressureDomain.mem_nhds hx))
  have hval := hQ.tendsto_comp (hq _ (show shiftedField a₀ x d₀ ∈ pressureDomain from hx))
    (show shiftedField a₀ x d₀ ∈ pressureDomain from hx) (tendsto_nhdsWithin_iff.2 ⟨hf,he⟩)
  exact hval.sub (((hX1.mul ha).mul (hd.pow 2)).div_const 2)

lemma meanField_tendsto_of_bounded_maximizers {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℕ → ℝ} {a₀ : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain) (hq : ContinuousOn q pressureDomain)
    (ha : Tendsto a atTop (𝓝 a₀)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    (hp : IsMeanField q a₀ p) {X : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x))
    (hXS : ∀ n, X n ∈ pressureDomain) {D : ℝ}
    (hatt : ∀ n, ∃ d ∈ Icc 0 D, quadraticCost (Q n) (a n) (X n) d = P n (X n)) :
    Tendsto (fun n => P n (X n)) atTop (𝓝 (p x)) := by
  choose d hd he using hatt
  apply metric_tendsto_of_subseq
  intro φ hφ
  obtain ⟨r,_,ψ,hψ,hr⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) D)).tendsto_subseq
    (fun n => hd (φ n))
  let θ := φ ∘ ψ
  have hθ := (hφ.comp hψ).tendsto_atTop
  have hlim := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ) hr hx (hX.comp hθ)
  have hle : quadraticCost q a₀ x r ≤ p x := (hp x hx).1 (mem_range_self r)
  have hge : p x ≤ quadraticCost q a₀ x r := by
    apply (hp x hx).2
    rintro _ ⟨s,rfl⟩
    have hs := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ)
      (tendsto_const_nhds (x := s)) hx (hX.comp hθ)
    apply le_of_tendsto_of_tendsto hs hlim
    exact Eventually.of_forall fun n => by
      change quadraticCost (Q (θ n)) (a (θ n)) (X (θ n)) s ≤
        quadraticCost (Q (θ n)) (a (θ n)) (X (θ n)) (d (θ n))
      rw [he]
      exact (hP (θ n) _ (hXS (θ n))).1 (mem_range_self s)
  have heq := le_antisymm hle hge
  refine ⟨ψ,hψ,?_⟩
  rw [heq] at hlim
  exact hlim.congr (fun n => he (θ n))

end ContinuumTemperature
end
end

end OAI
