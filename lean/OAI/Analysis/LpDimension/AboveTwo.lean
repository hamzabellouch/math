import OAI.Analysis.LpDimension.AboveParameters

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

lemma above_main_upper (p D : ℝ) (hp : 2 < p) (hD : 1 < D) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C*(Real.log (n:ℝ))^(1-2/p)) := by
  classical
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨R,hR,hRD⟩ := distortion_ratio p D hp0 hD
  let η := 1/(28*R)
  obtain ⟨hη,hηsmall⟩ := above_small_error R hR
  change 0 < η at hη
  change ((1+η)^3-1) ≤ 1/(2*R) at hηsmall
  obtain ⟨C₀,hC₀,hLaw⟩ := ramp_sum_bounded_law p η hp hη
  obtain ⟨A,hA,hParam⟩ := above_numeric_parameters p R C₀ ((1+η)^3-1) hp hR hC₀ hηsmall
  let C := (3+(4*p+1)/(1-2/p)+4*p*A)*4^(1-2/p)
  refine ⟨C,fun n hn => ?_⟩
  obtain ⟨ℓ,T,hT,hTK,hbR,hError⟩ := hParam n hn
  let H := 4*Real.log (n:ℝ)
  let J := (aboveVariance p+1)*H*2^(2*ℓ)
  let K := H^2*Real.exp (A*(H^(1-2/p)+1))
  let b := ∫ r, |dyadicRamp ℓ r|^p ∂pareto p
  let ε := b/R
  change T ≤ K at hTK
  change 1 ≤ ε at hbR
  change ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
    C₀*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ ε at hError
  have hH : 0 < H := by
    have hh := log_nat_lower n hn
    dsimp [H]
    linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity [aboveVariance_pos p hp]
  have hε : 0 < ε := zero_lt_one.trans_le hbR
  have hbε : R*ε ≤ b := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (show R ≠ 0 by linarith)]
  obtain ⟨hb,hDb⟩ := hRD b ε hε hbε
  let d := ⌈(K^p)^2*(H+1)⌉₊+1
  have hd : 0 < d := by dsimp [d]; omega
  have hgood : GoodDimension.{u} p n D d := by
    intro Ω mΩ ν x hx
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
    let : Nonempty (PairIndex n) := pairIndex_nonempty n hn
    let : Nonempty (Fin (n.choose 2)) := Fin.pos_iff_nonempty.mp (Nat.choose_pos hn)
    obtain ⟨y,hy⟩ := exact_discretization p hp1 n hn ν x hx
    let δ : PairIndex n → ℝ := fun e => ‖x e.val.1-x e.val.2‖
    have hδ (e : PairIndex n) : 0 < δ e :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => (ne_of_lt e.2) (hx he)))
    let B := normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ
    let g : Fin (n.choose 2) → PairIndex n → ℝ := fun a => B.mulVec (fun i => y i a)
    have hg : ∀ e, ∑ a, |g a e|^p = 1 :=
      normalized_coordinate_gradient p hp0 y δ hδ (fun e => hy e.val.1 e.val.2)
    have hw : ∀ w : PairIndex n → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
        ∃ μ : Measure (PairIndex n → ℝ), IsProbabilityMeasure μ ∧
          (∀ᵐ z ∂μ, ∃ v, B.mulVec v=z) ∧ (∀ᵐ z ∂μ, ∀ e, |z e| ≤ K) ∧
          (∑ e, w e*|(∫ z, |z e|^p ∂μ)-b|) ≤ ε := by
      intro w hw0 hws
      obtain ⟨μ,hμ,hRange,hBound,hErr⟩ :=
        hLaw (PairIndex n) (Fin n) (Fin (n.choose 2))
          (fun e => e.val.1) (fun e => e.val.2) δ w hδ hw0 hws
          (by simpa using hn) (pairIndex_incident n hn) (pairIndex_connected n)
          g hg (fun a => ⟨fun i => y i a,rfl⟩) ℓ T hT
      have hHn : (4*Real.log (Fintype.card (Fin n):ℝ)) = H := by simp [H]
      rw [hHn] at hErr
      refine ⟨μ,hμ,hRange,hBound.mono (fun z hz e => (hz e).trans hTK),?_⟩
      have hcard : (Fintype.card (PairIndex n):ℝ) ≤ (n:ℝ)^2 := by
        exact_mod_cast pairIndex_card_le_square n
      have htail := mul_le_mul_of_nonneg_left hcard
        (show 0 ≤ C₀*J^p*Real.exp (-T/(2*J)) by positivity)
      exact hErr.trans ((by linarith only [htail] :
        ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
          C₀*J^p*Real.exp (-T/(2*J))*(Fintype.card (PairIndex n):ℝ) ≤
        ((1+η)^3-1)*b+C₀*H^(p-2)*((ℓ:ℝ)+1)+
          C₀*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2).trans hError)
    have hprob : (2*Fintype.card (PairIndex n):ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1 :=
      sampling_probability_estimate (K^p) ε (Real.rpow_pos_of_pos hK _) hbR n _ hn
        Fintype.card_pos (pairIndex_card_le_square n)
    obtain ⟨z,hz⟩ := weighted_gradient_measure_samples B p K b ε hp0 hK.le hε hw d hd hprob
    obtain ⟨s,hs,hse⟩ := sampled_labels_embedding p D b ε hp0 (by linarith) hb hDb hd δ hδ z hz
    refine ⟨fun i a => z a i,s,hs,?_⟩
    exact all_pairs_of_edge_bounds p D s hp0 x (fun i a => z a i) hse
  have hdim : dimension.{u} p n D ≤ d := Nat.sInf_le hgood
  have hr : 0 < 1-2/p := by
    apply sub_pos.mpr
    exact (div_lt_one hp0).mpr hp
  have hnumer := sampling_dimension_estimate p (1-2/p) A hp0 hr hA.le n hn
  exact (show (dimension.{u} p n D:ℝ) ≤ d by exact_mod_cast hdim).trans hnumer

end SubpolynomialLp

end

end OAI
