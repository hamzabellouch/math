import OAI.Probability.DilutedSpin.HierarchyBasic
import OAI.Probability.DilutedSpin.QTreeLaw

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}
open scoped BigOperators

theorem leafProduct_single (n : ℕ) (f : FinitePath Ω n → ℝ) (x : Sample Ω (single n)) :
    leafProduct (single n) f x = f (singlePath n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∏ i : Fin 1, leafProduct (single n) (fun y => f ((x i).1,y)) (x i).2) = _
    rw [Fintype.prod_subsingleton]
    exact ih _ _

private theorem leafProduct_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (f : FinitePath Ω (n+1) → ℝ) (x : Ω × Sample Ω S') :
    leafProduct S' (fun y => f (x.1,y)) x.2 =
    leafProduct S (fun y => f ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,y))
      (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2 := by
  subst S'
  rfl

/-- Exactly one terminal factor is added by growth, and its ancestry is the
new path, not a path chosen by equality of sample values. -/
theorem leafProduct_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω (grow S v)) :
    leafProduct (grow S v) f x = leafProduct S f (oldSample S v x) * f (newPath S v x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (∏ j : Fin (k+1), leafProduct (Fin.cases (single n) C j)
        (fun y => f ((x j).1,y)) (x j).2) = _
      erw [Fin.prod_univ_succ]
      have hh := leafProduct_single n (fun y => f ((x 0).1,y)) (x 0).2
      calc
        _ = f ((x 0).1,singlePath n (x 0).2) *
            ∏ i : Fin k, leafProduct (C i) (fun y => f ((x i.succ).1,y)) (x i.succ).2 :=
          congrArg₂ (· * ·) hh rfl
        _ = _ := mul_comm _ _
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      have hp (j : Fin k) :
          leafProduct (C' j) (fun y => f ((x j).1,y)) (x j).2 =
          leafProduct (C j) (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 *
              if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 1 := by
        by_cases hj : j = i
        · subst j
          have hcast := leafProduct_cast (grow (C i) v) (C' i)
            (Function.update_self ..) f (x i)
          let y : Ω × Sample Ω (grow (C i) v) :=
            cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
          have hh := ih i v (fun z => f (y.1,z)) y.2
          have he : leafProduct (C' i) (fun z => f ((x i).1,z)) (x i).2 =
              leafProduct (C i) (fun z => f (y.1,z)) (oldSample (C i) v y.2) *
                f (y.1,newPath (C i) v y.2) := hcast.trans hh
          erw [oldSample.eq_1, newPath.eq_1]
          dsimp only [id]
          simp only [dite_true, ite_true]
          exact he
        · have hc := leafProduct_cast (C j) (C' j) (Function.update_of_ne hj ..) f (x j)
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hj, ite_eq_right hj, mul_one]
          exact hc
      change (∏ j, leafProduct (C' j) (fun y => f ((x j).1,y)) (x j).2) = _
      calc
        _ = ∏ j, (leafProduct (C j)
            (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 *
            if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 1) :=
          Finset.prod_congr rfl (fun j _ => hp j)
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ i)]; rfl


end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Terminal moment of a genuine prescribed tree, then expectation over Q. -/
noncomputable def qMoment {n : ℕ} (m : Fin (n+1) → ℝ) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) : ℝ :=
  qExpect m (fun R => (sampleLaw R T).expect (leafProduct R D)) k S

omit [Fintype Ω] in
theorem abs_leafProduct_le_one {n : ℕ} (S : PrescribedTree n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (x : Sample Ω S) :
    |leafProduct S D x| ≤ 1 := by
  rw [leafProduct_eq_prod, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hD _)

theorem abs_qMoment_le_one {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (k : ℕ) (S : PrescribedTree n) : |qMoment m T D k S| ≤ 1 :=
  abs_qExpect_le m hm hpos hroot hend (fun R =>
    FiniteLaw.abs_expect_le _ (abs_leafProduct_le_one R D hD)) k S

/-- Exact coefficients of all genuine fresh growth histories. Normalizing at
successive tree sizes produces the rising factorial, with no guessed law. -/
theorem extensionIterate_eq_qMoment {n : ℕ} (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (T : KernelTower Ω n)
    (D : FinitePath Ω n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    extensionIterate T m D k S (leafProduct S D) 0 =
      (-1:ℝ)^k * ((leaves S).ascFactorial k:ℝ) * qMoment m T D k S := by
  induction k generalizing S with
  | zero => simp [extensionIterate, fullyProtected_zero S T m hnz, qMoment, qExpect]
  | succ k ih =>
    change (∑ v : Internal S, gamma S m v *
      extensionIterate T m D k (grow S v)
        (fun x => leafProduct S D (oldSample S v x) * D (newPath S v x)) 0) = _
    have hg (v : Internal S) : (fun x => leafProduct S D (oldSample S v x) *
        D (newPath S v x)) = leafProduct (grow S v) D :=
      funext (fun x => (leafProduct_grow S v D x).symm)
    simp_rw [hg, ih, leaves_grow]
    have hfac : ((leaves S).ascFactorial (k+1):ℝ) =
        (leaves S:ℝ) * ((leaves S+1).ascFactorial k:ℝ) := by
      rw [Nat.ascFactorial_succ]
      exact_mod_cast (Nat.succ_ascFactorial (leaves S) k).symm
    rw [hfac]
    change _ = _ * (∑ v : Internal S, (-gamma S m v / leaves S) *
      qMoment m T D k (grow S v))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have hn : (leaves S:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (leaves_pos S))
    rw [pow_succ]
    field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators

theorem analyticAt_expect (P : FiniteLaw Ω) {f : ℝ → Ω → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => P.expect (f t)) u := by
  apply Finset.analyticAt_fun_sum
  intro x _
  exact analyticAt_const.mul (hf x)

theorem analyticAt_logMean (P : FiniteLaw Ω) (m : ℝ) {f : ℝ → Ω → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => P.logMean m (f t)) u := by
  have he : AnalyticAt ℝ (fun t => P.expMoment m (f t)) u :=
    P.analyticAt_expect (fun x => (analyticAt_const.mul (hf x)).rexp')
  exact (he.log (P.expMoment_pos m (f u))).div_const
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem analyticAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {f : ℝ → FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, AnalyticAt ℝ (fun t => f t x) u) :
    AnalyticAt ℝ (fun t => backwardLog n T m (f t)) u := by
  induction n with
  | zero => exact hf ()
  | succ n ih =>
    exact T.1.analyticAt_logMean (m 0)
      (fun x => ih (T.2 x) (fun j => m j.succ) (fun y => hf (x,y)))
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators Topology NNReal ENNReal
open Set Filter

noncomputable def logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) (t : ℝ) : ℝ :=
  KernelTower.backwardLog n T (fun j => m j.succ) (fun y => Real.log (1+t*D y))

noncomputable def logJet {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) : ℕ → ℝ → ℝ
  | 0 => logInsertion T m D
  | k+1 => extensionIterate T m D k (single n) (leafProduct (single n) D)

theorem fullyProtected_single {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) {u : ℝ} (hu : ∀ y, 0 < 1+u*D y) :
    fullyProtected (single n) T m D (leafProduct (single n) D) u =
      (KernelTower.law n (KernelTower.tilt n T (fun j => m j.succ)
        (fun y => Real.log (1+u*D y)))).expect (fun y => D y / (1+u*D y)) := by
  rw [fullyProtected]
  trans (sampleLaw (single n) (KernelTower.tilt n T (fun j => m j.succ)
    (fun y => Real.log (1+u*D y)))).expect
      (fun x => D (singlePath n x) / (1+u*D (singlePath n x)))
  · apply FiniteLaw.expect_congr
    intro x
    rw [leafProduct_single, leafSum_single, Real.exp_neg, Real.exp_log (hu _)]
    rfl
  · exact single_expect (Ω := Ω) n _ (fun y => D y / (1+u*D y))

theorem hasDerivAt_logJet {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (k : ℕ) {u : ℝ} (hu : ∀ y, 0 < 1+u*D y) :
    HasDerivAt (logJet T m D k) (logJet T m D (k+1) u) u := by
  cases k with
  | zero =>
    change HasDerivAt (logInsertion T m D)
      (fullyProtected (single n) T m D (leafProduct (single n) D) u) u
    rw [fullyProtected_single T m D hu]
    apply KernelTower.hasDerivAt_backwardLog n T _ hnz
    intro y
    simpa only [zero_add, one_mul, Pi.add_apply, id_eq] using
      ((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_id u).mul_const (D y))).log
        (ne_of_gt (hu y))
  | succ k => exact hasDerivAt_extensionIterate T m hnz hroot hend D k _ _ u hu

omit [Fintype Ω] in
theorem insertion_pos {n : ℕ} (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {u : ℝ} (hu : |u| < 1) (y : FinitePath Ω n) : 0 < 1+u*D y := by
  have h : |u * D y| ≤ |u| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg u)).trans_eq (mul_one _)
  have hb := (abs_le.mp h).1
  linarith

theorem iteratedDeriv_logInsertion {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    EqOn (iteratedDeriv k (logInsertion T m D)) (logJet T m D k) (Ioo (-1) 1) := by
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
    intro u hu
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (logInsertion T m D) =ᶠ[𝓝 u] logJet T m D k :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo (-1) 1, isOpen_Ioo.mem_nhds hu, ih⟩
    rw [he.deriv_eq]
    exact (hasDerivAt_logJet T m hnz hroot hend D k
      (insertion_pos D hD (abs_lt.mpr hu))).deriv

 
theorem logInsertion_coefficient {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    iteratedDeriv (k+1) (logInsertion T m D) 0 / ((k+1).factorial:ℝ) =
      (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) := by
  rw [iteratedDeriv_logInsertion T m hnz hroot hend D hD (k+1) (by norm_num)]
  change extensionIterate T m D k (single n) (leafProduct (single n) D) 0 / _ = _
  rw [extensionIterate_eq_qMoment m hnz T D k, leaves_single, Nat.one_ascFactorial,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk1 : (k:ℝ)+1 ≠ 0 := by positivity
  field_simp

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators Topology NNReal ENNReal
open Set Filter

theorem logInsertion_zero {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (D : FinitePath Ω n → ℝ) :
    logInsertion T m D 0 = 0 := by
  simp only [logInsertion, zero_mul, add_zero, Real.log_one]
  exact KernelTower.backwardLog_const n T _ hnz 0

theorem logInsertion_coefficient_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (k : ℕ) :
    |iteratedDeriv k (logInsertion T m D) 0 / (k.factorial:ℝ)| ≤ 1 := by
  cases k with
  | zero => simp [logInsertion_zero T m hnz D]
  | succ k =>
    rw [logInsertion_coefficient T m hnz hroot hend D hD k, abs_mul, abs_div,
      abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity : (0:ℝ) < k+1)]
    calc
      _ ≤ 1 / ((k:ℝ)+1) * 1 := mul_le_mul_of_nonneg_left
        (abs_qMoment_le_one m hm hpos hroot hend T D hD k (single n)) (by positivity)
      _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem analyticAt_logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {t : ℝ} (ht : |t| < 1) : AnalyticAt ℝ (logInsertion T m D) t := by
  apply KernelTower.analyticAt_backwardLog
  intro y
  exact (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).log
    (insertion_pos D hD ht y)

/-- The positive Q tree expansion of the nonlinear power means, valid on the
whole physical |t|<1 disk, not merely its unspecified Taylor neighborhood. -/
theorem hasSum_logInsertion {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k => (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1))
      (logInsertion T m D t) := by
  let c (k : ℕ) := iteratedDeriv k (logInsertion T m D) 0 / (k.factorial:ℝ)
  let p := FormalMultilinearSeries.ofScalars ℝ c
  have hrad : 1 ≤ p.radius := by
    exact p.le_radius_of_bound (r := (1:ℝ≥0)) 1 (fun k => by
      simpa only [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
        NNReal.coe_one, one_pow, mul_one] using
        logInsertion_coefficient_bound T m hm hpos hnz hroot hend D hD k)
  have ha : AnalyticOn ℝ (logInsertion T m D) (Metric.eball 0 1) := by
    intro x hx
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at hx
    exact (analyticAt_logInsertion T m D hD (by simpa [Real.dist_eq] using hx)).analyticWithinAt
  have hp : HasFPowerSeriesOnBall (logInsertion T m D) p 0 1 :=
    ha.hasFPowerSeriesOnSubball (by norm_num) hrad
  have htt : t ∈ Metric.eball (0:ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using ht
  have hs : HasSum (fun k => c k * t^k) (logInsertion T m D t) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, sub_zero,
      smul_eq_mul] using hp.hasSum_sub htt
  have hc0 : c 0 * t^0 = 0 := by simp [c, logInsertion_zero T m hnz D]
  have hs' : HasSum (fun k => c (k+1) * t^(k+1)) (logInsertion T m D t) := by
    simpa only [Finset.sum_range_one, hc0, sub_zero] using
      (hasSum_nat_add_iff' 1).mpr hs
  simpa only [c, logInsertion_coefficient T m hnz hroot hend D hD] using hs'

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
open scoped BigOperators

theorem logInsertion_term_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) (t : ℝ) (k : ℕ) :
    |(-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)| ≤
      |t|^(k+1) / (k+1) := by
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0:ℝ) < k+1), abs_pow]
  calc
    _ ≤ (1 / ((k:ℝ)+1) * 1) * |t|^(k+1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (abs_qMoment_le_one m hm hpos hroot hend T D hD k (single n))
        (by positivity)) (by positivity)
    _ = _ := by ring

 
theorem logInsertion_tail_bound {n : ℕ} (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1) {t : ℝ} (ht : |t| < 1) (K : ℕ) :
    |logInsertion T m D t - ∑ k ∈ Finset.range K,
      (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)| ≤
        ∑' k : ℕ, |t|^(k+K+1) / (k+K+1) := by
  let f (k : ℕ) := (-1:ℝ)^k / (k+1) * qMoment m T D k (single n) * t^(k+1)
  let g (k : ℕ) := |t|^(k+1) / (k+1)
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le (fun k => by dsimp [g]; positivity) _
      ((summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left |t|)
    intro k
    dsimp [g]
    rw [pow_succ, mul_comm]
    exact div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hs : HasSum f (logInsertion T m D t) :=
    hasSum_logInsertion T m hm hpos hnz hroot hend D hD ht
  have htail : logInsertion T m D t - ∑ k ∈ Finset.range K, f k =
      ∑' k, f (k+K) := by
    rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add K]
    ring
  change |logInsertion T m D t - ∑ k ∈ Finset.range K, f k| ≤ _
  rw [htail]
  have hgtail : Summable (fun k => g (k+K)) := (summable_nat_add_iff K).mpr hg
  have hftail : Summable (fun k => f (k+K)) := (summable_nat_add_iff K).mpr hs.summable
  have hb := hftail.abs.tsum_le_tsum (fun k =>
    logInsertion_term_bound T m hm hpos hroot hend D hD t (k+K))
      hgtail
  have habsn : Summable (fun k => ‖f (k+K)‖) := by
    simpa only [Real.norm_eq_abs] using hftail.abs
  have habs : |∑' k, f (k+K)| ≤ ∑' k, |f (k+K)| := by
    simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm habsn)
  exact habs.trans (by simpa only [f, g, Nat.cast_add, Nat.cast_one] using hb)

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance finiteLogExpansionDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier

/-- Suppression of unary vertices loses neither the leveled tree nor labels. -/
theorem exists_realize {r : ℕ} (T : PrescribedTree r) (d : ℕ) :
    ∃ (S : ReducedTopology) (q : S.Vertex → ℕ),
      Admissible S q d (d+r) ∧ realize r d S q=T := by
  induction T generalizing d with
  | leaf => exact ⟨.leaf,Empty.elim,trivial,rfl⟩
  | @node r k C ih =>
    classical
    by_cases hk : (k:ℕ)=1
    · have hk' : k=1 := Subtype.ext hk
      subst k
      obtain ⟨S,q,hq,he⟩ := ih 0 (d+1)
      refine ⟨S,q,?_,?_⟩
      · exact admissible_mono_lower S q (lo := d+1) (Nat.le_succ d) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq)
      · rw [realize_unary_of_later]
        · rw [he]
          unfold PrescribedTree.unary
          congr 1
          funext i
          have hi : i=0 := Fin.ext (by have h := i.isLt; change i.val<1 at h; simp only [Fin.val_zero]; omega)
          rw [hi]
        · intro v
          have := admissible_lower S q hq v
          omega
    · have hk2 : 2≤(k:ℕ) := by have := k.pos; omega
      choose S q hq he using fun i => ih i (d+1)
      let Q : (ReducedTopology.node k hk2 S).Vertex → ℕ :=
        fun v => match v with | none => d | some ⟨i,w⟩ => q i w
      refine ⟨.node k hk2 S,Q,?_,?_⟩
      · refine ⟨le_rfl,by change d<d+(r+1); omega,?_⟩
        intro i
        simpa only [Q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq i
      · simp only [realize,Q,lt_self_iff_false,ite_false]
        congr 1
        funext i
        exact he i

/-- For bounded leaf number there are finitely many possible reduced shapes. -/
theorem exists_bounded_realize {r : ℕ} (T : PrescribedTree r) (K : ℕ)
    (hK : T.leaves≤K) :
    ∃ (S : ReducedTopology), S∈boundedTopologies K ∧
      ∃ q : S.Vertex → Fin r,
        Admissible S (fun v => q v) 0 r ∧ realize r 0 S (fun v => q v)=T := by
  obtain ⟨S,q,ha,he⟩ := exists_realize T 0
  have hc : Fintype.card S.Leaf≤K := by
    rw [← realize_leaves r 0 S q ha,he]
    exact hK
  refine ⟨S,mem_boundedTopologies K S hc,fun v => ⟨q v,?_⟩,by simpa using ha,he⟩
  simpa using admissible_upper S q ha v

end DilutedSpinGlass.ReducedTopology

end

end OAI
