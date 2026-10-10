import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestDistance

namespace OAI

namespace MetricKMedianRecovery.PriceTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

lemma baseline_dual_le (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X) (a : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (ha : activeAt loc t z Q a) :
    openingDual loc t z Q i (fun _ => z) a ≤ bidRow loc t z Q i := by
  classical
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte,clippedAt_of_active loc t z Q j ht hj]
    exact le_rfl
  · simp only [hj,↓reduceIte,clippedAt_of_inactive loc t z Q j ht hj]
    exact max_le_max (capped_triangle_row loc t z Q i a j ht ht1
      (inactive_nonempty loc t z Q j hj) (fun f hf => (ha f hf).le)) le_rfl

theorem tight_dual_openable (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (tau : D → ℝ) (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hbox : ∀ j, activeAt loc (1-3*v) z Q j →
      z ≤ tau j ∧ tau j ≤ (1+v^2)*z ∧ ∀ f ∈ Q, tau j ≤ (1-3*v)*dist (loc j) f)
    (i : X) (a : D) (ha : activeAt loc (1-3*v) z Q a)
    (htight : openingDual loc (1-3*v) z Q i tau a = lam)
    (hrows : ∀ k ∈ F, ∀ b, activeAt loc (1-3*v) z Q b →
      openingDual loc (1-3*v) z Q k tau b ≤ lam) :
    etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i := by
  classical
  let newtau : D → ℝ := fun j => if dist i (loc j) ≤ v*z then tau j else z
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  have hsmall : ∀ j, activeAt loc (1-3*v) z Q j → newtau j ≤ tau j := by
    intro j hj
    dsimp only [newtau]
    split_ifs
    · exact le_rfl
    · exact (hbox j hj).1
  have hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i newtau := by
    intro j hj
    refine ⟨?_,?_,?_,?_⟩
    · dsimp only [newtau]; split_ifs
      · exact (hbox j hj).1
      · exact le_rfl
    · exact (hsmall j hj).trans (hbox j hj).2.1
    · intro f hf
      exact (hsmall j hj).trans ((hbox j hj).2.2 f hf)
    · intro hfar
      simp only [newtau,ite_eq_right (not_le.mpr hfar)]
  have hpay : openingDual loc (1-3*v) z Q i tau a ≤
      openingPayment loc (1-3*v) z Q i newtau := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q j
    · simp only [hj,↓reduceIte]
      apply max_le_max _ le_rfl
      dsimp only [newtau]
      split_ifs with hnear
      · have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x:=i) (y:=loc j))
        linarith only [hd]
      · have hfar : v*z ≤ dist i (loc j) := (not_le.mp hnear).le
        have hm := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 3*v)
        have hb := (hbox j hj).2.1
        nlinarith only [hm,hb,mul_nonneg (sq_nonneg v) hz.le]
    · simp only [hj,↓reduceIte]
      have hh := capped_triangle_row loc (1-3*v) (tau a) Q i a j ht ht1
        (inactive_nonempty loc (1-3*v) z Q j hj) (hbox a ha).2.2
      have hd := mul_le_mul_of_nonneg_right ht1 (dist_nonneg (x:=i) (y:=loc j))
      exact max_le_max (by linarith only [hh,hd]) le_rfl
  refine ⟨newtau,hadm,?_,?_⟩
  · simpa only [mul_zero,sub_zero,htight] using hpay
  · intro k hk b hb
    apply le_trans _ (hrows k hk b hb)
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : activeAt loc (1-3*v) z Q j
    · simp only [hj,↓reduceIte]
      exact max_le_max (sub_le_sub_right (hsmall j hj) _) le_rfl
    · simp only [hj,↓reduceIte]
      exact max_le_max (by linarith only [hsmall b hb]) le_rfl

lemma continuous_payment (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X)
    (tau : ℝ → D → ℝ) (hc : ∀ j, Continuous (fun x => tau x j)) :
    Continuous (fun x => openingPayment loc t z Q i (tau x)) := by
  classical
  unfold openingPayment
  apply continuous_finsetSum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    exact ((hc j).sub continuous_const).max continuous_const
  · simp only [hj,↓reduceIte]
    exact continuous_const

lemma continuous_dual (loc : D → X) (Q : Finset X) (t z : ℝ) (i : X) (a : D)
    (tau : ℝ → D → ℝ) (hc : ∀ j, Continuous (fun x => tau x j)) :
    Continuous (fun x => openingDual loc t z Q i (tau x) a) := by
  classical
  unfold openingDual
  apply continuous_finsetSum
  intro j _
  by_cases hj : activeAt loc t z Q j
  · simp only [hj,↓reduceIte]
    exact ((hc j).sub continuous_const).max continuous_const
  · simp only [hj,↓reduceIte]
    exact (((hc a).sub continuous_const).sub continuous_const).max continuous_const

theorem payment_produces_openable (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (hbase : ∀ i ∈ F, bidRow loc (1-3*v) z Q i ≤ lam)
    (i : X) (hi : i ∈ F) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z Q i tau)
    (hpaid : lam ≤ openingPayment loc (1-3*v) z Q i tau) :
    ∃ k ∈ F, etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 k := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : z ≤ (1+v^2)*z := by nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  let bids : ℝ → D → ℝ := fun x j => z+x*(tau j-z)
  have hbids : ∀ x ∈ Set.Icc (0:ℝ) 1,
      admissibleBids loc (1-3*v) (1+v^2) v z Q i (bids x) := by
    intro x hx j hj
    obtain ⟨hlo,hhi,hcap,hfar⟩ := hadm j hj
    dsimp only [bids]
    have hxlo := mul_nonneg hx.1 (sub_nonneg.mpr hlo)
    have hxhi := mul_le_mul_of_nonneg_right hx.2 (sub_nonneg.mpr hlo)
    refine ⟨by linarith only [hxlo],by linarith only [hxhi,hhi],?_,?_⟩
    · intro f hf
      linarith only [hxhi,hcap f hf]
    · intro hh
      rw [hfar hh]
      ring
  have hb0 : bids 0 = fun _ => z := by funext j; simp [bids]
  have hb1 : bids 1 = tau := by funext j; simp [bids]
  have hbcont : ∀ j, Continuous (fun x => bids x j) := by
    intro j
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hd0 : ∀ k ∈ F, ∀ a, activeAt loc (1-3*v) z Q a →
      openingDual loc (1-3*v) z Q k (bids 0) a ≤ lam := by
    intro k hk a ha
    rw [hb0]
    exact (baseline_dual_le loc Q (1-3*v) z k a ht ht1 ha).trans (hbase k hk)
  by_cases hp0 : lam ≤ openingPayment loc (1-3*v) z Q i (bids 0)
  · exact ⟨i,hi,bids 0,hbids 0 ⟨le_rfl,by norm_num⟩,by simpa using hp0,hd0⟩
  let Idx := Unit ⊕ (↥F × D)
  let row : ℝ → Idx → ℝ := fun x r => match r with
    | .inl _ => openingPayment loc (1-3*v) z Q i (bids x)
    | .inr (k,a) => if activeAt loc (1-3*v) z Q a then
        openingDual loc (1-3*v) z Q k (bids x) a else 0
  have hrowcont : ∀ r, Continuous (fun x => row x r) := by
    intro r
    cases r with
    | inl => exact continuous_payment loc Q (1-3*v) z i bids hbcont
    | inr r =>
      dsimp only [row]
      split_ifs
      · exact continuous_dual loc Q (1-3*v) z r.1 r.2 bids hbcont
      · exact continuous_const
  have hu : (Finset.univ : Finset Idx).Nonempty := ⟨Sum.inl (),Finset.mem_univ _⟩
  let M : ℝ → ℝ := fun x => Finset.univ.sup' hu (row x)
  have hcont : Continuous M := Continuous.finset_sup'_apply hu (fun r _ => hrowcont r)
  have hM0 : M 0 ≤ lam := by
    apply Finset.sup'_le hu
    intro r _
    cases r with
    | inl => exact (lt_of_not_ge hp0).le
    | inr r =>
      dsimp only [row]
      split_ifs with ha
      · exact hd0 r.1 r.1.property r.2 ha
      · exact hlam.le
  have hM1 : lam ≤ M 1 := by
    calc
      _ ≤ row 1 (.inl ()) := by simpa only [row,hb1] using hpaid
      _ ≤ M 1 := Finset.le_sup' (row 1) (Finset.mem_univ (Sum.inl ()))
  obtain ⟨x,hx,hMx⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1)
    hcont.continuousOn ⟨hM0,hM1⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup' hu (row x)
  have heq : row x r = lam := hr.symm.trans hMx
  have hrows : ∀ k ∈ F, ∀ a, activeAt loc (1-3*v) z Q a →
      openingDual loc (1-3*v) z Q k (bids x) a ≤ lam := by
    intro k hk a ha
    have hh := (Finset.le_sup' (row x) (Finset.mem_univ (Sum.inr (⟨k,hk⟩,a)))).trans_eq hMx
    simpa only [row,ite_eq_left ha] using hh
  cases r with
  | inl => exact ⟨i,hi,bids x,hbids x hx,by simpa only [row,mul_zero,sub_zero] using heq.ge,hrows⟩
  | inr r =>
    dsimp only [row] at heq
    split_ifs at heq with ha
    · refine ⟨r.1,r.1.property,tight_dual_openable loc F Q v z lam (bids x) hv hvsmall hz ?_
        r.1 r.2 ha heq hrows⟩
      intro j hj
      exact ⟨(hbids x hx j hj).1,(hbids x hx j hj).2.1,(hbids x hx j hj).2.2.1⟩
    · exact (hlam.ne heq).elim

end MetricKMedianRecovery.PriceTransfer

end OAI
