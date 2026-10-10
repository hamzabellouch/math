import OAI.Analysis.LpDimension.SamplingBounds

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

lemma below_main_upper (p D : ℝ) (hp : 1 < p) (hp2 : p < 2) (hD : 1 < D) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      (dimension.{u} p n D : ℝ) ≤ Real.exp (C*(Real.log (n:ℝ))^(2-p)) := by
  classical
  have hp0 : 0 < p := by linarith
  let c := stableConstant p
  have hc : 0 < c := stableConstant_pos p hp0 hp2
  obtain ⟨μ,hμ⟩ := exists_stable_law_full p hp0 hp2
  obtain ⟨k,hk,hTail⟩ := stable_tail_lower (μ : Measure ℝ) p c hp0 hp2 hc
    (fun t => by rw [hμ t, Complex.exp_ofReal_re])
  obtain ⟨R,hR,hRD⟩ := distortion_ratio p D hp0 hD
  let C0 := p*(2*c*2^p)*(1+1/(p-1))+96*c
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  let A := R*(C0+1)/(k*p)
  have hA : 0 < A := by dsimp [A]; positivity
  let C := (3+(4*p+1)/(2-p)+4*p*A)*4^(2-p)
  refine ⟨C,fun n hn => ?_⟩
  let H := 4*Real.log (n:ℝ)
  have hH : 0 < H := by
    have hh := log_nat_lower n hn
    dsimp [H]; linarith
  let T := H*Real.exp (A*(H^(2-p)+1))
  have hT : 0 < T := by dsimp [T]; positivity
  let K := H^2*Real.exp (A*(H^(2-p)+1))
  have hK : 0 < K := by dsimp [K]; positivity
  let ε := (C0+1)*(H^(2-p)+1)
  have hε1 : 1 ≤ ε := by
    have ht : 0 ≤ H^(2-p) := Real.rpow_nonneg hH.le _
    dsimp [ε]
    nlinarith
  have hε : 0 < ε := zero_lt_one.trans_le hε1
  let b := ∫ x, (min |x| (T/H))^p ∂(μ:Measure ℝ)
  have ha : 1 ≤ T/H := by
    dsimp [T]
    rw [mul_div_cancel_left₀ _ hH.ne']
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hbR : R*ε ≤ b := by
    have hh := capped_moment_lower_log (μ:Measure ℝ) p k (T/H) hp hk.le ha hTail
    have he : k*p*Real.log (T/H) = R*ε := by
      dsimp [T]
      rw [mul_div_cancel_left₀ _ hH.ne', Real.log_exp]
      dsimp [A, ε]
      field_simp
    rwa [he] at hh
  obtain ⟨hb,hDb⟩ := hRD b ε hε hbR
  let d := ⌈(K^p)^2*(H+1)⌉₊+1
  have hd : 0 < d := by dsimp [d]; omega
  have hgood : GoodDimension.{u} p n D d := by
    intro Ω mΩ ν x hx
    let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
    let : Nonempty (PairIndex n) := pairIndex_nonempty n hn
    obtain ⟨y,hy⟩ := exact_discretization p hp n hn ν x hx
    let δ : PairIndex n → ℝ := fun e => ‖x e.val.1-x e.val.2‖
    have hδ (e : PairIndex n) : 0 < δ e :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => (ne_of_lt e.2) (hx he)))
    let B := normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ
    let g : Fin (n.choose 2) → PairIndex n → ℝ := fun a => B.mulVec (fun i => y i a)
    have hg : ∀ e, ∑ a, |g a e|^p = 1 :=
      normalized_coordinate_gradient p hp0 y δ hδ (fun e => hy e.val.1 e.val.2)
    have hw : ∀ w : PairIndex n → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
        ∃ F : (Fin (n.choose 2) → ℝ) → PairIndex n → ℝ, Measurable F ∧
          (∀ r, ∃ z, B.mulVec z = F r) ∧ (∀ r e, |F r e| ≤ K) ∧
          (∑ e, w e*|(∫ r, |F r e|^p ∂Measure.pi (fun _ : Fin (n.choose 2) => (μ:Measure ℝ)))-b|) ≤ ε := by
      intro w hw0 hws
      obtain ⟨F,hFm,hFV,hFb,hFe⟩ := stable_gradient_weighted (μ:Measure ℝ) p c hp hp2 hc hμ
        (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ w hδ hw0 hws
        (by simpa using hn) (pairIndex_incident n hn) (pairIndex_connected n)
        g (fun a => ⟨fun i => y i a,rfl⟩) hg T hT
      have hHn : (4*Real.log (Fintype.card (Fin n):ℝ)) = H := by simp [H]
      rw [hHn] at hFb hFe
      refine ⟨F,hFm,hFV,?_,?_⟩
      · have he : H*T = K := by dsimp [T,K]; ring
        simpa only [he] using hFb
      · have he : C0*H^(2-p) ≤ ε := by
          have ht : 0 ≤ H^(2-p) := Real.rpow_nonneg hH.le _
          dsimp [ε]; nlinarith
        exact hFe.trans he
    have hprob : (2*Fintype.card (PairIndex n):ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1 :=
      sampling_probability_estimate (K^p) ε (Real.rpow_pos_of_pos hK _) hε1 n _ hn
        Fintype.card_pos (pairIndex_card_le_square n)
    obtain ⟨z,hz⟩ := weighted_gradient_samples
      (Measure.pi (fun _ : Fin (n.choose 2) => (μ:Measure ℝ))) B p K b ε hp0 hK.le hε hw d hd hprob
    obtain ⟨s,hs,hse⟩ := sampled_labels_embedding p D b ε hp0 (by linarith) hb hDb hd δ hδ z hz
    refine ⟨fun i a => z a i,s,hs,?_⟩
    exact all_pairs_of_edge_bounds p D s hp0 x (fun i a => z a i) hse
  have hdim : dimension.{u} p n D ≤ d := Nat.sInf_le hgood
  have hnumer := sampling_dimension_estimate p (2-p) A hp0 (by linarith) hA.le n hn
  exact (show (dimension.{u} p n D:ℝ) ≤ d by exact_mod_cast hdim).trans hnumer

end SubpolynomialLp

end

end OAI
