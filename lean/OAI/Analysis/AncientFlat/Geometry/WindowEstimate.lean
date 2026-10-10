import OAI.Analysis.AncientFlat.Evolution.NearConstant
import OAI.Analysis.AncientFlat.Geometry.WindowJets
import OAI.Analysis.AncientFlat.Geometry.WindowGeometry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLocalization
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma unscale_top [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {α q B : ℝ} (hq : 0<q) (p0 : V × ℝ) (S : Set (V × ℝ))
    (u : ℝ → V → ℂ) (hs : ∀ t, ContDiff ℝ 4 (u t))
    (h : HolderBound α S (fun p => iteratedFDeriv ℝ 4 (windowValue p0 q u p.2) p.1) (q^4*q^α*B)) :
    (∀ p∈S, ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1‖≤B*q^α) ∧
    (∀ p∈S, ∀ z∈S,
      ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1-
        iteratedFDeriv ℝ 4 (u (window p0 q z).2) (window p0 q z).1‖≤B*pdist (window p0 q p) (window p0 q z)^α) := by
  have hq4 : 0<q^4 := pow_pos hq _
  constructor
  · intro p hp
    have hh := h.1 p hp
    dsimp only at hh
    rw [window_jet p0 q u hs 4 le_rfl,norm_smul,Real.norm_of_nonneg hq4.le] at hh
    apply (mul_le_mul_iff_right₀ hq4).mp
    nlinarith [hh]
  · intro p hp z hz
    have hh := h.2 p hp z hz
    dsimp only at hh
    rw [window_jet p0 q u hs 4 le_rfl,window_jet p0 q u hs 4 le_rfl,←smul_sub,norm_smul,
      Real.norm_of_nonneg hq4.le] at hh
    rw [pdist_window p0 hq.le,Real.mul_rpow hq.le (pdist_nonneg p z)]
    apply (mul_le_mul_iff_right₀ hq4).mp
    nlinarith [hh]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem window_fourth_estimate (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (q : ℝ), 0<q → q≤1 → K*(4*q)^α≤δ →
      ∀ (p0 : V × ℝ) (Ω : Set (V × ℝ)), p0∈Ω → MapsTo (window p0 q) (cylinder 4) Ω →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α Ω a K → HolderBound α Ω b K → (∀ p∈Ω, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α Ω u ut M) →
      HolderBound α Ω (fun p => f p.2 p.1) F → (∀ p∈Ω, ‖u p.2 p.1‖≤U) →
      (∀ p∈Ω, ∀ z∈Ω,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤H*pdist p z^α) →
      (∀ p∈Ω, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      let B := θ*H+(C/(q^4*q^α))*(F+U)
      (∀ p∈cylinder 1, ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1‖≤B*q^α) ∧
      (∀ p∈cylinder 1, ∀ z∈cylinder 1,
        ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1-
          iteratedFDeriv ℝ 4 (u (window p0 q z).2) (window p0 q z).1‖≤B*pdist (window p0 q p) (window p0 q z)^α) := by
  obtain ⟨δ,C,hδ,_,hC,Hlocal⟩ := near_constant_fourth (V := V) α κ K θ hα hα1 hκ hK hθ
  refine ⟨δ,C,hδ,hC,?_⟩
  intro q hq hq1 hsmall p0 Ω hp0 hm a b ha hb hella u ut f F U H hF hU hH hs hd hj hf hu hh he
  have h2 : (cylinder 2 : Set (V × ℝ))⊆cylinder 4 := cylinder_mono (by norm_num) (by norm_num)
  have Hosc (p : V × ℝ) (hp : p∈cylinder 2) : ‖a p0-a (window p0 q p)‖≤δ := by
    have hdist : pdist p0 (window p0 q p)≤4*q := by
      conv_lhs => arg 1; rw [←window_zero p0 q]
      rw [pdist_window p0 hq.le]
      have hb := cylinder_pdist_zero (by norm_num : (0:ℝ)≤2) hp
      nlinarith
    exact (ha.2 p0 hp0 _ (hm (h2 hp))).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pdist_nonneg _ _) hdist hα.le) hK).trans hsmall)
  have Hj : ∃ M, 0≤M ∧ JetBound α (cylinder 4) (windowValue p0 q u) (windowTime p0 q ut) M := by
    obtain ⟨M,hM,hj⟩ := hj
    exact ⟨M,hM,window_jet_bound hα.le hM hq hq1 p0 u ut hs hj hm⟩
  have Hloc := Hlocal (a p0) (hella p0 hp0) ((le_abs_self _).trans (ha.1 p0 hp0))
    (fun p => a (window p0 q p)) (fun p => q^4 • b (window p0 q p))
    (holder_window hα.le hq hq1 p0 ha hm) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm) Hosc
    (windowValue p0 q u) (windowTime p0 q ut) (windowTime p0 q f) F U (q^4*q^α*H)
    hF hU (by positivity) (windowValue_contDiff p0 q u hs)
    (fun p hp => window_hasDerivAt p0 q u ut p (hd _ (hm hp))) Hj
    (holder_window_smul hα.le hF hq hq1 p0 4 hf hm) (fun p hp => hu _ (hm hp))
    (window_top_seminorm hq p0 u hs hh hm) (fun p hp => window_equation p0 q a b u ut f hs p (he _ (hm hp)))
  have heq : θ*(q^4*q^α*H)+C*(F+U)=q^4*q^α*(θ*H+C/(q^4*q^α)*(F+U)) := by
    have hqa : q^α≠0 := (Real.rpow_pos_of_pos hq _).ne'
    field_simp
  rw [heq] at Hloc
  exact unscale_top hq p0 (cylinder 1) u hs Hloc
end ParabolicLocalization

end

end OAI
