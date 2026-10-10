import OAI.Analysis.LipschitzHilbert.Estimates.ConstructedSynthesisNeighborhood
import OAI.Analysis.LipschitzHilbert.Estimates.TopCovariantData
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeTopNeighborhood

namespace OAI

/-! Global top concentration for the actual covariant derivative. The
original analyzing integrals are retained when synthesis is differentiated. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_covariant_top (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone cutoff → ∀ (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      ∀ data : TopRawPacketData P lo hi T K D, TopCovariantData data → ∀ J L : ℝ,
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          (4*(K*T.width))*‖covariantSignal data.frequency (fun k t =>
            planarPacketInterval (P.mainCoefficient cutoff v g)
              (fun j u k y x => P.wave j u k y x) a b z.1 t k)
                ((z.2-T.slope*z.1)+w)‖ ≤
              (P.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := constructed_synthesis_global_neighborhood hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P cutoff v hv g hg hg1 hd T K D hK data second J L
  let raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ := fun i =>
    if i=0 then data.raw 1 else second.second
  have hderiv y j u k x : ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
      (lineEnvelope (P.centerX j u) (P.length j) 3 x *
        lineEnvelope (P.centerZ j u) P.width 2 y) := by
    rw [← data.wave_eq j u k y]
    apply (data.derivative_bound 0 y j u k x).trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
    exact mul_le_mul (lineEnvelope_antitone _ _ _ (by omega : 3 ≤ 3+2*(8*D+1)))
      (lineEnvelope_antitone _ _ _ (by omega : 2 ≤ 2+2*(8*D+1)))
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  let I := {ab : ℕ × ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : I → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval (P.mainCoefficient cutoff v g)
      (fun j u k t s => data.raw 1 j u k t s) ab.val.1 ab.val.2 x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T K
    (P.topPacketAmplitude Ab Am D) J L D hK (P.topPacketAmplitude_pos Ab Am D).le F (by
      intro n hn
      obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P cutoff v hv g hg hg1 hd hderiv
        (fun j u k y ξ hξ => by rw [← data.wave_eq j u k y]; exact data.low 0 y j u k ξ hξ)
        (fun j u k y ξ hξ => by rw [← data.wave_eq j u k y]; exact data.high 0 y j u k ξ hξ)
        raw data.frequency T.x (T.y-T.slope*T.x) (K*T.length) (K*T.width) (8*D+1)
        (mul_pos hK T.length_pos) (mul_pos hK T.width_pos) (by omega)
        data.length_le data.width_le data.centerX_le data.centerZ_le
        (by
          intro i y j u k x
          fin_cases i
          · simpa [raw] using data.bound 1 y j u k x
          · simpa [raw] using second.bound y j u k x)
        (by
          intro i y j u k x
          fin_cases i
          · simpa [raw] using data.derivative_bound 1 y j u k x
          · simpa [raw] using second.derivative_bound y j u k x)
        (by
          intro i y j u k ξ hξ
          fin_cases i
          · simpa [raw] using data.low 1 y j u k ξ hξ
          · simpa [raw] using second.low y j u k ξ hξ)
        (by
          intro i y j u k ξ hξ
          fin_cases i
          · simpa [raw] using data.high 1 y j u k ξ hξ
          · simpa [raw] using second.high y j u k ξ hξ)
        (by
          intro y j u k x
          simpa [raw, Complex.ofReal_mul] using second.covariant y j u k x)
        (by
          intro i j u k
          fin_cases i
          · simpa [raw] using data.continuous 1 j u k
          · simpa [raw] using second.continuous j u k)
        (by
          intro j u k x y
          simpa [raw] using second.differentiable j u k x y) n hn
      refine ⟨bad,hbad,harea,?_⟩
      intro ab x y w hw hout
      have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x y w hw hout
      simp only [Nat.add_sub_cancel, raw, ↓reduceIte] at hp
      convert hp using 1
      dsimp [F,topPacketAmplitude]
      ring)
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb z w hw hout
  have hp := hpoint (⟨(a,b),hab,hb⟩ : I) z w hw hout
  have heq := planarPacketInterval_scaled_covariant_eq (P.mainCoefficient cutoff v g)
    (fun j u k y x => P.wave j u k y x) (fun j u k y x => data.raw 1 j u k y x)
    data.frequency (4*(K*T.width)) a b z.1 ((z.2-T.slope*z.1)+w)
    (by
      intro j u k t
      simpa only [data.wave_eq] using data.differentiable j u k z.1 t)
    (by
      intro j u k
      simpa [data.wave_eq, Complex.ofReal_mul] using
        data.covariant ((z.2-T.slope*z.1)+w) j u k z.1)
  change ‖planarPacketInterval (P.mainCoefficient cutoff v g)
    (fun j u k y x => data.raw 1 j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤ _ at hp
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by
    have := T.width_pos
    positivity)] at hp
  exact hp

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
