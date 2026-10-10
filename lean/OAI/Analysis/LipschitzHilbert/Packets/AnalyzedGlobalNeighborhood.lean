import OAI.Analysis.LipschitzHilbert.Packets.AnalyzedNeighborhood
import OAI.Analysis.LipschitzHilbert.Estimates.GlobalLocalNeighborhood
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketLocality

namespace OAI

/-! Full-plane neighborhood control for the actual integral-defined
analyzing coefficients and polynomially localized synthesis packets. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem analyzed_global_neighborhood (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)),
      Monotone d →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (C r : ℝ), 0 < C → 0 < r →
      (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => synth 0 j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
      ∀ (raw : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (baseX baseZ rx : ℝ) (q : ℕ),
      0 < rx → 1 ≤ q → P.topLength ≤ rx →
      (∀ j u k y x, synth 0 j u k y x =
        (polynomialWeight baseX rx q x*polynomialWeight baseZ r q y : ℝ)*raw j u k y x) →
      ∀ (branching : ℕ), 1 < branching → ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
          (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r))*ENNReal.ofReal ((4*Real.pi)^2) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w, |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
            raw a b x (z+w)‖ ≤
              256^q*(24*K*(n:ℝ))*boxVariationWeight (packetBoxIndex baseX baseZ rx r x z)^(q-1) := by
  obtain ⟨Ab,Am,hAb,hAm,hlocal⟩ := analyzed_interval_neighborhood hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hderiv hd hlow hhigh synth frequency C r hC hr
    hbound hdbound hslow hshigh hcov hcont hdiff hD raw baseX baseZ rx q hrx hq hwidth
    hmult branching hbranch n hn
  dsimp only
  let coeff := fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u
  let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) branching
  let J := {ab : ℕ × ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : J → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval coeff raw ab.val.1 ab.val.2 x y
  have hK : 0 ≤ K := (lineMomentBase_pos _ _ _ hC.le (Nat.cast_nonneg _)).le
  have hall := global_top_neighborhood_of_local F baseX baseZ rx r (8*K) hrx hr
    (by positivity) (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r)) n q hn hq (by
      intro p m hm
      let grid : FiniteLineGrid := {
        branching := branching
        branching_pos := lt_trans Nat.zero_lt_one hbranch
        origin := baseX+rx*p.1
        width := rx
        width_pos := hrx
        depth := N }
      have hroot : grid.root = Ico (baseX+rx*p.1) (baseX+rx*((p.1:ℝ)+1)) := by
        unfold FiniteLineGrid.root
        dsimp [grid]
        congr 1
        ring
      have hvolume : grid.lineMeasure univ = ENNReal.ofReal rx := by
        rw [FiniteLineGrid.lineMeasure, Measure.restrict_apply_univ]
        unfold FiniteLineGrid.root
        rw [Real.volume_Ico]
        congr 1
        dsimp [grid]
        ring
      obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := hlocal N κ ι P d v hv g hg hg1 hderiv hd hlow hhigh
        synth frequency C (baseZ+r*p.2) r hC hr hbound hdbound hslow hshigh hcov hcont hdiff hD
        grid hbranch hwidth m hm
      refine ⟨bad,hbad,?_,?_⟩
      · rw [hvolume] at harea
        convert harea using 1
        ring
      · intro ab x z w hx hz hw hout
        have hx' : x ∈ grid.root := by rw [hroot]; exact hx
        have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x z w hx' hz hw hout
        have heq := planarPacketInterval_multiplier_norm coeff raw
          (fun j u k y x => synth 0 j u k y x)
          (fun x y => polynomialWeight baseX rx q x*polynomialWeight baseZ r q y)
          (fun x y => mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
            (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))) hmult ab.val.1 ab.val.2 x (z+w)
        rw [← heq]
        exact hp)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hall
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb x z w hw hout
  have hp := hpoint (⟨(a,b),hab,hb⟩ : J) x z w hw hout
  convert hp using 1
  congr 2
  ring

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
