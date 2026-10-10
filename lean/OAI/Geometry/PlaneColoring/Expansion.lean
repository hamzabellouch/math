import Mathlib

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma positive_log_difference_bound {u v m C : ℝ} (hm : 0 < m)
    (hu : m ≤ u) (hv : m ≤ v) (hC : 0 ≤ C) (hd : |u-v| ≤ C) :
    |Real.log u-Real.log v| ≤ C/m := by
  have hu' : 0 < u := hm.trans_le hu
  have hv' : 0 < v := hm.trans_le hv
  have haux : ∀ a b : ℝ, m ≤ a → m ≤ b → a-b ≤ C → Real.log a-Real.log b ≤ C/m := by
    intro a b ha hb hab
    have ha' := hm.trans_le ha
    have hb' := hm.trans_le hb
    have h := Real.log_le_sub_one_of_pos (div_pos ha' hb')
    rw [Real.log_div ha'.ne' hb'.ne'] at h
    have he : a/b-1=(a-b)/b := by field_simp
    rw [he] at h
    exact h.trans ((div_le_div_of_nonneg_right hab hb'.le).trans
      (div_le_div_of_nonneg_left hC hm hb))
  exact abs_le.mpr ⟨by have h := haux v u hv hu (by linarith [neg_le_abs (u-v)]); linarith,
    haux u v hu hv (le_trans (le_abs_self _) hd)⟩
lemma controlled_interval_derivative {f' : ℝ → ℝ} {K : ℝ≥0} {a b e : ℝ}
    (hlip : LipschitzWith K f') (_hab : a ≤ b) (he : (K : ℝ)*(b-a) ≤ e)
    (hmid : 1+e ≤ f' ((a+b)/2)) {t : ℝ} (ht : t ∈ Icc a b) :
    1+e/2 ≤ f' t := by
  have hdist : |t-(a+b)/2| ≤ (b-a)/2 := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
  have h := hlip.dist_le_mul t ((a+b)/2)
  rw [Real.dist_eq,Real.dist_eq] at h
  have hm := mul_le_mul_of_nonneg_left hdist K.2
  have hn := neg_le_abs (f' t-f' ((a+b)/2))
  nlinarith
lemma controlled_interval_expands {f f' : ℝ → ℝ} {K : ℝ≥0} {a b e : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hlip : LipschitzWith K f') (hab : a ≤ b)
    (he : (K : ℝ)*(b-a) ≤ e) (hmid : 1+e ≤ f' ((a+b)/2)) :
    (1+e/2)*(b-a) ≤ f b-f a := by
  apply (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) _ a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩ hab
  intro t ht
  rw [(hd t).deriv]
  exact controlled_interval_derivative hlip hab he hmid (interior_subset ht)
lemma geometric_partial_sum {l : ℕ → ℝ} {q : ℝ} (_hq : 1 < q)
    (h0 : 0 ≤ l 0) (hstep : ∀ n, q*l n ≤ l (n+1)) (N : ℕ) :
    (q-1)*(∑ n ∈ Finset.range N, l n) ≤ l N := by
  have h : (q-1)*(∑ n ∈ Finset.range N, l n) ≤ l N-l 0 := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,mul_add]
      nlinarith [hstep n]
  linarith
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
def iterComposition (f : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n+1 => fun x => f n (iterComposition f n x)
def iterDerivative (f D : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n+1 => fun x => D n (iterComposition f n x)*iterDerivative f D n x
variable {f D : ℕ → ℝ → ℝ}
lemma iterComposition_hasDeriv (hd : ∀ n x, HasDerivAt (f n) (D n x) x) (n : ℕ) (x : ℝ) :
    HasDerivAt (iterComposition f n) (iterDerivative f D n x) x := by
  induction n with
  | zero => exact hasDerivAt_id x
  | succ n ih => exact (hd n _).comp x ih
lemma iterDerivative_pos (hD : ∀ n x, 0 < D n x) (n : ℕ) (x : ℝ) :
    0 < iterDerivative f D n x := by
  induction n with
  | zero => norm_num [iterDerivative]
  | succ n ih => exact mul_pos (hD n _) ih
lemma iterComposition_strictMono (hd : ∀ n x, HasDerivAt (f n) (D n x) x)
    (hD : ∀ n x, 0 < D n x) (n : ℕ) : StrictMono (iterComposition f n) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(iterComposition_hasDeriv hd n x).deriv]
  exact iterDerivative_pos hD n x
lemma iterDerivative_log_oscillation (hd : ∀ n x, HasDerivAt (f n) (D n x) x)
    (hD : ∀ n x, (1/2 : ℝ) ≤ D n x) {K : ℝ≥0}
    (hK : ∀ n, LipschitzWith K (D n)) {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (N : ℕ) :
    |Real.log (iterDerivative f D N x)-Real.log (iterDerivative f D N y)| ≤
      2*(K : ℝ)*(∑ n ∈ Finset.range N, (iterComposition f n b-iterComposition f n a)) := by
  rcases K with ⟨K,hKpos⟩
  change |Real.log (iterDerivative f D N x)-Real.log (iterDerivative f D N y)| ≤
    2*K*(∑ n ∈ Finset.range N, (iterComposition f n b-iterComposition f n a))
  have hp : ∀ n t, 0 < D n t := fun n t => lt_of_lt_of_le (by norm_num) (hD n t)
  induction N with
  | zero => simp [iterDerivative]
  | succ n ih =>
    have hm := (iterComposition_strictMono hd hp n).monotone
    have hu := hm hx.1
    have hv := hm hx.2
    have hu' := hm hy.1
    have hv' := hm hy.2
    have hab : 0 ≤ iterComposition f n b-iterComposition f n a := by linarith
    have hdist : |iterComposition f n x-iterComposition f n y| ≤
        iterComposition f n b-iterComposition f n a := by
      rw [abs_le]; constructor <;> linarith
    have hkd := (hK n).dist_le_mul (iterComposition f n x) (iterComposition f n y)
    change |D n (iterComposition f n x)-D n (iterComposition f n y)| ≤
      K*|iterComposition f n x-iterComposition f n y| at hkd
    have hC := mul_nonneg hKpos hab
    have hh := positive_log_difference_bound (by norm_num : (0 : ℝ)<1/2)
      (hD n (iterComposition f n x)) (hD n (iterComposition f n y)) hC
      (hkd.trans (mul_le_mul_of_nonneg_left hdist hKpos))
    simp only [iterDerivative,Real.log_mul (hp n _).ne' (iterDerivative_pos hp n _).ne',
      Finset.sum_range_succ]
    have ht := abs_add_le (Real.log (D n (iterComposition f n x))-Real.log (D n (iterComposition f n y)))
      (Real.log (iterDerivative f D n x)-Real.log (iterDerivative f D n y))
    have he : Real.log (D n (iterComposition f n x)) + Real.log (iterDerivative f D n x) -
      (Real.log (D n (iterComposition f n y)) + Real.log (iterDerivative f D n y)) =
      (Real.log (D n (iterComposition f n x))-Real.log (D n (iterComposition f n y)))+
      (Real.log (iterDerivative f D n x)-Real.log (iterDerivative f D n y)) := by ring
    rw [he]
    exact ht.trans ((add_le_add hh ih).trans_eq (by ring))
lemma iterDerivative_ratio_bound (hd : ∀ n x, HasDerivAt (f n) (D n x) x)
    (hD : ∀ n x, (1/2 : ℝ) ≤ D n x) {K : ℝ≥0}
    (hK : ∀ n, LipschitzWith K (D n)) {a b x y M : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (N : ℕ) (hM : 2*(K : ℝ)*(∑ n ∈ Finset.range N, (iterComposition f n b-iterComposition f n a)) ≤ M) :
    iterDerivative f D N x ≤ Real.exp M * iterDerivative f D N y := by
  have hp : ∀ n t, 0 < D n t := fun n t => lt_of_lt_of_le (by norm_num) (hD n t)
  have h := (le_abs_self _).trans ((iterDerivative_log_oscillation hd hD hK hx hy N).trans hM)
  have hex := Real.exp_le_exp.mpr h
  rw [Real.exp_sub,Real.exp_log (iterDerivative_pos hp N x),Real.exp_log (iterDerivative_pos hp N y)] at hex
  exact (div_le_iff₀ (iterDerivative_pos hp N y)).mp hex
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set
namespace EuclideanFiveColor
lemma eventually_reaches_threshold {l : ℕ → ℝ} {q L : ℝ} (hq : 1 < q) (h0 : 0 < l 0)
    (hstep : ∀ n, l n < L → q*l n ≤ l (n+1)) : ∃ N, L ≤ l N := by
  by_contra hex
  have hlt : ∀ n, l n < L := fun n => lt_of_not_ge (fun h => hex ⟨n,h⟩)
  have hp : ∀ n, 0 < l n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact (mul_pos (lt_trans zero_lt_one hq) ih).trans_le (hstep n (hlt n))
  have hm : Monotone l := monotone_nat_of_le_succ fun n => by nlinarith [hstep n (hlt n),hp n]
  have hg : ∀ n : ℕ, (n : ℝ)*((q-1)*l 0) ≤ l n := by
    intro n
    induction n with
    | zero => simpa using h0.le
    | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one]
      have hl := hm (Nat.zero_le n)
      have h := hstep n (hlt n)
      have ht := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hq.le)
      nlinarith
  have hc : 0 < (q-1)*l 0 := mul_pos (sub_pos.mpr hq) h0
  obtain ⟨N,hN⟩ := exists_nat_gt (L/((q-1)*l 0))
  have hn : L < (N : ℝ)*((q-1)*l 0) := (div_lt_iff₀ hc).mp hN
  exact (hlt N).not_ge (hn.le.trans (hg N))
lemma first_expansion_threshold {l : ℕ → ℝ} {q U L : ℝ} (hq : 1 < q) (h0 : 0 < l 0)
    (hsmall : l 0 < L) (hU : 0 ≤ U)
    (hstep : ∀ n, l n < L → q*l n ≤ l (n+1))
    (hupper : ∀ n, l (n+1) ≤ U*l n) :
    ∃ N, L ≤ l N ∧ l N ≤ U*L ∧ (∀ n < N, l n < L) ∧
      (q-1)*(∑ n ∈ Finset.range N, l n) ≤ l N := by
  have hex := eventually_reaches_threshold hq h0 hstep
  let N := Nat.find hex
  have hN : L ≤ l N := Nat.find_spec hex
  have hbefore : ∀ n < N, l n < L := fun n hn => lt_of_not_ge (Nat.find_min hex hn)
  have hNpos : 0 < N := by
    by_contra h
    have hzero : N=0 := Nat.eq_zero_of_not_pos h
    rw [hzero] at hN
    exact hsmall.not_ge hN
  have hup : l N ≤ U*L := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
    rw [hn]
    exact (hupper n).trans (mul_le_mul_of_nonneg_left (hbefore n (by omega)).le hU)
  have hsum : ∀ n ≤ N, (q-1)*(∑ i ∈ Finset.range n, l i) ≤ l n-l 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep n (hbefore n (by omega))
      rw [Finset.sum_range_succ,mul_add]
      nlinarith
  exact ⟨N,hN,hup,hbefore,(hsum N le_rfl).trans (by linarith)⟩
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma exists_expanding_word {ι : Type*} {F D : ι → ℝ → ℝ} {K : ℝ≥0} {e U L a b : ℝ}
    (hd : ∀ j x, HasDerivAt (F j) (D j x) x)
    (hp : ∀ j x, (1/2 : ℝ) ≤ D j x) (hup : ∀ j x, D j x ≤ U)
    (hK : ∀ j, LipschitzWith K (D j)) (hlarge : ∀ x, ∃ j, 1+e ≤ D j x)
    (he : 0 < e) (hKL : (K : ℝ)*L ≤ e) (hU : 0 ≤ U)
    (hab : a < b) (hsmall : b-a < L) :
    ∃ w : ℕ → ι, ∃ N : ℕ,
      L ≤ iterComposition (fun n => F (w n)) N b-iterComposition (fun n => F (w n)) N a ∧
      iterComposition (fun n => F (w n)) N b-iterComposition (fun n => F (w n)) N a ≤ U*L ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
        iterDerivative (fun n => F (w n)) (fun n => D (w n)) N x ≤
          Real.exp (4*(K : ℝ)*U*L/e)*iterDerivative (fun n => F (w n)) (fun n => D (w n)) N y := by
  choose j hj using hlarge
  let A : ℕ → ℝ × ℝ := fun n => Nat.rec (a,b)
    (fun _ p => (F (j ((p.1+p.2)/2)) p.1,F (j ((p.1+p.2)/2)) p.2)) n
  let w : ℕ → ι := fun n => j (((A n).1+(A n).2)/2)
  let f : ℕ → ℝ → ℝ := fun n => F (w n)
  let d : ℕ → ℝ → ℝ := fun n => D (w n)
  have hd' : ∀ n x, HasDerivAt (f n) (d n x) x := fun n x => hd (w n) x
  have hp' : ∀ n x, 0 < d n x := fun n x => (by norm_num : (0 : ℝ)<1/2).trans_le (hp (w n) x)
  have hends : ∀ n, (A n).1=iterComposition f n a ∧ (A n).2=iterComposition f n b := by
    intro n
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      change f n (A n).1=iterComposition f (n+1) a ∧ f n (A n).2=iterComposition f (n+1) b
      rw [ih.1,ih.2]
      exact ⟨rfl,rfl⟩
  let l : ℕ → ℝ := fun n => iterComposition f n b-iterComposition f n a
  have hpos : ∀ n, 0 < l n := fun n => sub_pos.mpr (iterComposition_strictMono hd' hp' n hab)
  have hstep : ∀ n, l n < L → (1+e/2)*l n ≤ l (n+1) := by
    intro n hln
    apply controlled_interval_expands (hd' n) (hK (w n))
      (iterComposition_strictMono hd' hp' n hab).le
    · exact (mul_le_mul_of_nonneg_left hln.le K.2).trans hKL
    · simpa only [d,w,(hends n).1,(hends n).2] using hj (((A n).1+(A n).2)/2)
  have hupper : ∀ n, l (n+1) ≤ U*l n := by
    intro n
    exact image_sub_le_mul_sub_of_deriv_le (fun x => (hd' n x).differentiableAt)
      (fun x => by rw [(hd' n x).deriv]; exact hup (w n) x)
      (iterComposition_strictMono hd' hp' n hab).le
  obtain ⟨N,hN,hNu,_,hsum⟩ := first_expansion_threshold (by linarith : 1 < 1+e/2)
    (hpos 0) hsmall hU hstep hupper
  refine ⟨w,N,hN,hNu,fun x hx y hy => ?_⟩
  apply iterDerivative_ratio_bound hd' (fun n x => hp (w n) x) (fun n => hK (w n)) hx hy N
  change 2*(K : ℝ)*(∑ n ∈ Finset.range N, l n) ≤ 4*(K : ℝ)*U*L/e
  apply (le_div_iff₀ he).mpr
  have hsum' : e/2*(∑ n ∈ Finset.range N, l n) ≤ U*L := by
    simpa only [add_sub_cancel_left] using hsum.trans hNu
  have hmul := mul_le_mul_of_nonneg_left hsum' (by positivity : (0 : ℝ)≤4*(K : ℝ))
  nlinarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma line_lipschitzOn_image_bound {f : ℝ → ℝ} {s : Set ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) : volume (f '' s) ≤ (K : ℝ≥0∞)*volume s := by
  have h := hf.hausdorffMeasure_image_le (by norm_num : (0 : ℝ)≤1)
  simpa only [hausdorffMeasure_real,ENNReal.rpow_one] using h
lemma interval_defect_image_bound {f : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0} {A : Set ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (hm : MonotoneOn f (Icc a b))
    (hK : LipschitzOnWith K f (Icc a b))
    (hA : ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ f x ∈ A) :
    volume (Icc (f a) (f b) \ A) ≤ (K : ℝ≥0∞)*volume (Icc a b \ A) := by
  let E : Set ℝ := {x ∈ Icc a b | ¬(x ∈ A ↔ f x ∈ A)}
  have hE : volume E=0 := measure_mono_null (fun _ h => h.2) (ae_iff.mp hA)
  have hEi : volume (f '' E)=0 := by
    have h := line_lipschitzOn_image_bound (hK.mono (show E ⊆ Icc a b from fun _ h => h.1))
    rw [hE,mul_zero] at h
    exact le_antisymm h bot_le
  have hsub : Icc (f a) (f b) \ A ⊆ f '' (Icc a b \ A) ∪ f '' E := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := (hc.image_Icc_of_monotoneOn hab hm ▸ hy.1 : y ∈ f '' Icc a b)
    by_cases hxA : x ∈ A
    · right
      exact ⟨x,⟨hx,fun h => hy.2 (hxy ▸ h.mp hxA)⟩,hxy⟩
    · exact Or.inl ⟨x,⟨hx,hxA⟩,hxy⟩
  calc
    volume (Icc (f a) (f b) \ A) ≤ volume (f '' (Icc a b \ A) ∪ f '' E) := measure_mono hsub
    _ ≤ volume (f '' (Icc a b \ A))+volume (f '' E) := measure_union_le _ _
    _ = volume (f '' (Icc a b \ A)) := by rw [hEi,add_zero]
    _ ≤ (K : ℝ≥0∞)*volume (Icc a b \ A) := line_lipschitzOn_image_bound (hK.mono sdiff_subset)
lemma derivative_ratio_lipschitzOn {f D : ℝ → ℝ} {a b R : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (D x) x) (hp : ∀ x, 0 < D x) (hR : 0 ≤ R)
    (hratio : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, D x ≤ R*D y) :
    LipschitzOnWith (Real.toNNReal (R*((f b-f a)/(b-a)))) f (Icc a b) := by
  obtain ⟨z,hz,he⟩ := exists_hasDerivAt_eq_slope f D hab
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (hd x).differentiableAt)
  intro x hx
  rw [(hd x).deriv]
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by rw [← he]; exact mul_nonneg hR (hp z).le),coe_nnnorm,Real.norm_eq_abs,abs_of_pos (hp x)]
  rw [← he]
  exact hratio x hx z ⟨hz.1.le,hz.2.le⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma line_volume_preimage_bound {F : ℝ → ℝ} {s : Set (ℝ)} {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (A : Set (ℝ)) :
    volume (F ⁻¹' A ∩ s) ≤ (K : ENNReal) * volume A := by
  have he : Subtype.val '' ((s.domRestrict F) ⁻¹' A) = F ⁻¹' A ∩ s := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨hq,q.2⟩
    · rintro ⟨hp,hs⟩; exact ⟨⟨p,hs⟩,hp,rfl⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤1)) ((s.domRestrict F) ⁻¹' A)
  have ha := hF.hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤1) A
  rw [he,hausdorffMeasure_real] at hi
  rw [← hi,hausdorffMeasure_real,ENNReal.rpow_one] at ha
  exact ha
lemma line_map_restrict_volume_le {F : ℝ → ℝ} (hm : Measurable F)
    {s B : Set (ℝ)} (_hB : MeasurableSet B) {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (himage : MapsTo F s B) :
    (volume.restrict s).map F ≤ (K : ENNReal) • volume.restrict B := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hm hA,Measure.restrict_apply (hm hA),Measure.smul_apply,
    Measure.restrict_apply hA,smul_eq_mul]
  have he : F ⁻¹' A ∩ s = F ⁻¹' (A ∩ B) ∩ s := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1,himage hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
  rw [he]
  exact line_volume_preimage_bound hF (A ∩ B)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [NormalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integrable_comp_of_map_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => f (T x)) μ := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  exact (integrable_map_measure hh.aestronglyMeasurable hT.aemeasurable).mp hh
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integral_norm_comp_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    (∫ x, ‖f (T x)‖ ∂μ) ≤ (C : ℝ)*(∫ y, ‖f y‖ ∂ν) := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  rw [← integral_map hT.aemeasurable hh.norm.aestronglyMeasurable]
  calc
    _ ≤ ∫ y, ‖f y‖ ∂((C : ENNReal) • ν) :=
      integral_mono_measure hmap (Eventually.of_forall fun y => norm_nonneg _) (hf.norm.smul_measure (by simp))
    _ = _ := by rw [integral_smul_measure]; simp
/-- L¹ continuity under measurable perturbations with a common bounded pushforward density. -/
lemma tendsto_integral_norm_comp_sub [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ n, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(3*((C : ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hgT (n : ℕ) : Integrable (fun x => g (T n x)) μ :=
    integrable_comp_of_map_le (hT n) (hmT n) hgi
  have hgS : Integrable (fun x => g (S x)) μ := integrable_comp_of_map_le hS hmS hgi
  have hfT (n : ℕ) := integrable_comp_of_map_le (hT n) (hmT n) hf
  have hfS := integrable_comp_of_map_le hS hmS hf
  have hmid : Tendsto (fun n => ∫ x, ‖g (T n x)-g (S x)‖ ∂μ) atTop (𝓝 0) := by
    have hp := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 2*‖g‖)
      (fun n => ((hgT n).sub hgS).norm.aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (T n x),g.norm_coe_le_norm (S x)]))
      (ht.mono fun x hx => by
        have hh := (g.continuous.tendsto (S x)).comp hx
        simpa using (hh.sub tendsto_const_nhds).norm)
    simpa using hp
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hmid (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 : (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le (hT n) (hmT n) (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have h2 : (∫ x, ‖f (S x)-g (S x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le hS hmS (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have htri : (∫ x, ‖f (T n x)-f (S x)‖ ∂μ) ≤
      (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) + (∫ x, ‖g (T n x)-g (S x)‖ ∂μ) +
      (∫ x, ‖f (S x)-g (S x)‖ ∂μ) := by
    have ha : Integrable (fun x => ‖f (T n x)-g (T n x)‖) μ := ((hfT n).sub (hgT n)).norm
    have hb : Integrable (fun x => ‖g (T n x)-g (S x)‖) μ := ((hgT n).sub hgS).norm
    have hc : Integrable (fun x => ‖f (S x)-g (S x)‖) μ := (hfS.sub hgS).norm
    have hi := integral_mono ((hfT n).sub hfS).norm ((ha.add hb).add hc) (fun x => by
      simpa only [Pi.add_apply,Pi.sub_apply,← dist_eq_norm,dist_comm (g (S x))] using
        dist_triangle4 (f (T n x)) (g (T n x)) (g (S x)) (f (S x)))
    apply hi.trans_eq
    exact (integral_add (ha.add hb) hc).trans (congrArg (fun t => t + ∫ x, ‖f (S x)-g (S x)‖ ∂μ) (integral_add ha hb))
  have hδv : (C : ℝ)*δ ≤ ε/3 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<3*((C : ℝ)+1))).mpr
    nlinarith [C.2]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have hm := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hm
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
lemma tendsto_integral_norm_comp_sub_eventual {X Y : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [NormalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ᶠ n in atTop, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmT
  apply (tendsto_add_atTop_iff_nat N).mp
  apply tendsto_integral_norm_comp_sub (T := fun n => T (n+N)) (C := C)
    (fun n => hT (n+N)) hS (fun n => hN _ (Nat.le_add_left N n)) hmS
  · exact ht.mono fun x hx => (tendsto_add_atTop_iff_nat N).mpr hx
  · exact hf
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
lemma line_antilipschitz_qmp {S : ℝ → ℝ} (hS : Measurable S) {I : Set ℝ} {K : ℝ≥0}
    (hA : AntilipschitzWith K (I.domRestrict S)) :
    Measure.QuasiMeasurePreserving S (volume.restrict I) volume := by
  refine ⟨hS,?_⟩
  have hle := line_map_restrict_volume_le hS MeasurableSet.univ hA (mapsTo_univ S I)
  rw [Measure.restrict_univ] at hle
  exact Measure.absolutelyContinuous_of_le_smul hle
lemma line_indicator_pullback_L1 {T : ℕ → ℝ → ℝ} {S : ℝ → ℝ} {I B D : Set ℝ} {K : ℝ≥0}
    [IsFiniteMeasure (volume.restrict I)] [IsFiniteMeasure (volume.restrict B)]
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hB : IsCompact B) (hD : MeasurableSet D)
    (hAT : ∀ᶠ n in atTop, AntilipschitzWith K (I.domRestrict (T n)))
    (hAS : AntilipschitzWith K (I.domRestrict S))
    (hBT : ∀ᶠ n in atTop, MapsTo (T n) I B) (hBS : MapsTo S I B)
    (ht : ∀ᵐ x ∂volume.restrict I, Tendsto (fun n => T n x) atTop (𝓝 (S x))) :
    Tendsto (fun n => ∫ x in I, ‖D.indicator (fun _ => (1 : ℝ)) (T n x)-
      D.indicator (fun _ => (1 : ℝ)) (S x)‖) atTop (𝓝 0) := by
  have : (volume.restrict B).WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top hB.measure_lt_top.ne
  apply tendsto_integral_norm_comp_sub_eventual (ν := volume.restrict B) (C := K) hT hS
  · filter_upwards [hAT,hBT] with n ha hb
    exact line_map_restrict_volume_le (hT n) hB.measurableSet ha hb
  · exact line_map_restrict_volume_le hS hB.measurableSet hAS hBS
  · exact ht
  · exact (integrable_const (1 : ℝ)).indicator hD
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma deriv_lower_antilipschitz {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : AntilipschitzWith 2 f := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this y x (le_of_not_ge hxy)
  have hm := mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact hp x) hxy
  have hmono : f x ≤ f y := le_of_sub_nonneg (by nlinarith)
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),
    abs_of_nonpos (sub_nonpos.mpr hmono)]
  norm_num
  linarith
lemma deriv_lower_qmp {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : Measure.QuasiMeasurePreserving f volume volume := by
  have hA := (deriv_lower_antilipschitz hd hp).comp
    ((isometry_subtype_coe : Isometry (Subtype.val : {x : ℝ // x ∈ (univ : Set ℝ)} → ℝ)).antilipschitzWith)
  simpa only [Measure.restrict_univ] using
    (line_antilipschitz_qmp (I := univ) (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).measurable hA)
lemma iterComposition_invariant {f : ℕ → ℝ → ℝ} {A : Set ℝ}
    (hq : ∀ n, Measure.QuasiMeasurePreserving (f n) volume volume)
    (hA : ∀ n, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ f n x ∈ A) (N : ℕ) :
    ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ iterComposition f N x ∈ A := by
  have hq' : ∀ n, Measure.QuasiMeasurePreserving (iterComposition f n) volume volume := by
    intro n
    induction n with
    | zero => exact Measure.QuasiMeasurePreserving.id _
    | succ n ih => exact (hq n).comp ih
  induction N with
  | zero => exact Filter.Eventually.of_forall (fun x => Iff.rfl)
  | succ N ih =>
    filter_upwards [ih,(hq' N).ae (hA N)] with x hx hxx
    exact hx.trans hxx
lemma expanding_interval_defect {ι : Type*} {F D : ι → ℝ → ℝ}
    {K : ℝ≥0} {e U L a b : ℝ} {A : Set ℝ}
    (hd : ∀ j x, HasDerivAt (F j) (D j x) x)
    (hp : ∀ j x, (1/2 : ℝ) ≤ D j x) (hup : ∀ j x, D j x ≤ U)
    (hK : ∀ j, LipschitzWith K (D j)) (hlarge : ∀ x, ∃ j, 1+e ≤ D j x)
    (he : 0 < e) (hKL : (K : ℝ)*L ≤ e) (hU : 0 ≤ U)
    (hinv : ∀ j, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ F j x ∈ A)
    (hab : a < b) (hsmall : b-a < L) :
    ∃ a' b' : ℝ, L ≤ b'-a' ∧ b'-a' ≤ U*L ∧
      volume (Icc a' b' \ A) ≤ ENNReal.ofReal (Real.exp (4*(K : ℝ)*U*L/e)*U*L/(b-a))*
        volume (Icc a b \ A) := by
  obtain ⟨w,N,hN,hNu,hr⟩ := exists_expanding_word hd hp hup hK hlarge he hKL hU hab hsmall
  let f := fun n => F (w n)
  let G := iterComposition f N
  have hd' := iterComposition_hasDeriv (fun n x => hd (w n) x) N
  have hp' := iterDerivative_pos (f := f) (fun n x => lt_of_lt_of_le (by norm_num) (hp (w n) x)) N
  have hm := iterComposition_strictMono (fun n x => hd (w n) x)
    (fun n x => lt_of_lt_of_le (by norm_num) (hp (w n) x)) N
  have hLip := derivative_ratio_lipschitzOn hab hd' hp' (Real.exp_pos _).le hr
  have hAi := iterComposition_invariant (fun n => deriv_lower_qmp (hd (w n)) (hp (w n)))
    (fun n => hinv (w n)) N
  refine ⟨G a,G b,hN,hNu,?_⟩
  apply (interval_defect_image_bound hab.le
    (fun x _ => (hd' x).continuousAt.continuousWithinAt) (hm.monotone.monotoneOn _) hLip hAi).trans
  gcongr
  change ENNReal.ofReal _ ≤ ENNReal.ofReal _
  apply ENNReal.ofReal_le_ofReal
  have := mul_le_mul_of_nonneg_left hNu (Real.exp_pos (4*(K : ℝ)*U*L/e)).le
  calc
    Real.exp (4*(K : ℝ)*U*L/e)*((G b-G a)/(b-a)) =
      (Real.exp (4*(K : ℝ)*U*L/e)*(G b-G a))/(b-a) := by ring
    _ ≤ Real.exp (4*(K : ℝ)*U*L/e)*U*L/(b-a) := by
      apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
      simpa only [mul_assoc] using this
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma periodic_interval_defect {A : Set ℝ} {P : ℝ}
    (hper : ∀ (n : ℤ) x, x+(n : ℝ)*P ∈ A ↔ x ∈ A) (n : ℤ) (a b : ℝ) :
    volume (Icc (a-(n : ℝ)*P) (b-(n : ℝ)*P) \ A) = volume (Icc a b \ A) := by
  have he : Icc (a-(n : ℝ)*P) (b-(n : ℝ)*P) \ A =
      (fun x : ℝ => x+(n : ℝ)*P) ⁻¹' (Icc a b \ A) := by
    ext x
    simp only [mem_preimage,Set.mem_sdiff,mem_Icc,hper]
    constructor <;> rintro ⟨⟨h₁,h₂⟩,h₃⟩ <;> exact ⟨⟨by linarith,by linarith⟩,h₃⟩
  rw [he,measure_preimage_add_right]
lemma periodic_interval_normalize {A : Set ℝ} {P : ℝ} (hP : 0 < P)
    (hper : ∀ (n : ℤ) x, x+(n : ℝ)*P ∈ A ↔ x ∈ A) (a b : ℝ) :
    ∃ a' b' : ℝ, a' ∈ Icc 0 P ∧ b'-a'=b-a ∧
      volume (Icc a' b' \ A)=volume (Icc a b \ A) := by
  let n : ℤ := ⌊a/P⌋
  refine ⟨a-(n : ℝ)*P,b-(n : ℝ)*P,?_,by ring,periodic_interval_defect hper n a b⟩
  have h := Int.fract_div_mul_self_mem_Ico P a hP
  have he : Int.fract (a/P)*P=a-(n : ℝ)*P := by
    change (a/P-(⌊a/P⌋ : ℝ))*P=a-(⌊a/P⌋ : ℝ)*P
    field_simp
  rw [he] at h
  exact ⟨h.1,h.2.le⟩
lemma compact_almost_conull_interval {A : Set ℝ} {P L : ℝ}
    {a b : ℕ → ℝ} (hL : 0 < L) (ha : ∀ n, a n ∈ Icc 0 P)
    (hl : ∀ n, L ≤ b n-a n)
    (hdef : Tendsto (fun n => volume (Icc (a n) (b n) \ A)) atTop (𝓝 0)) :
    ∃ x y : ℝ, y-x=L/2 ∧ volume (Icc x y \ A)=0 := by
  obtain ⟨z,hz,φ,hφ,hzlim⟩ := isCompact_Icc.tendsto_subseq ha
  have he : ∀ᶠ n in atTop, Icc (z+L/4) (z+3*L/4) ⊆ Icc (a (φ n)) (b (φ n)) := by
    have hdist := (Metric.tendsto_nhds.mp hzlim) (L/4) (by positivity)
    filter_upwards [hdist] with n hn
    rw [Real.dist_eq,abs_lt] at hn
    dsimp only [Function.comp_apply] at hn
    intro x hx
    have hh := hl (φ n)
    constructor <;> linarith [hx.1,hx.2]
  have hle : ∀ᶠ n in atTop, volume (Icc (z+L/4) (z+3*L/4) \ A) ≤
      volume (Icc (a (φ n)) (b (φ n)) \ A) := he.mono (fun _ h => measure_mono (sdiff_subset_sdiff_left h))
  refine ⟨z+L/4,z+3*L/4,by ring,?_⟩
  exact le_antisymm (ge_of_tendsto (hdef.comp hφ.tendsto_atTop) hle) bot_le
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace EuclideanFiveColor
lemma exists_density_interval {A : Set ℝ} (hA : MeasurableSet A) (hpos : volume A ≠ 0)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ a b : ℝ, a < b ∧ b-a < L ∧
      volume (Icc a b \ A) ≤ ENNReal.ofReal ε*ENNReal.ofReal (b-a) := by
  have h := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (volume : Measure ℝ) hA.compl
  obtain ⟨x,hx,ht⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae h)
  have hx' : x ∉ Aᶜ := by simpa using hx
  simp only [indicator_of_notMem hx'] at ht
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hev := ht.eventually (gt_mem_nhds he)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < L/2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ)<L/2)).filter_mono nhdsWithin_le_nhds
  have hev' : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ r < L/2 ∧ volume (Aᶜ ∩ Metric.closedBall x r)/volume (Metric.closedBall x r)<ENNReal.ofReal ε := by
    filter_upwards [self_mem_nhdsWithin,hev,hsmall] with r hr hh hs
    exact ⟨hr,hs,hh⟩
  obtain ⟨r,hr,hs,hh⟩ := hev'.exists
  refine ⟨x-r,x+r,by linarith,by linarith,?_⟩
  rw [Real.closedBall_eq_Icc] at hh
  have heq : Aᶜ ∩ Icc (x-r) (x+r)=Icc (x-r) (x+r) \ A := by ext; simp [and_comm]
  rw [heq,Real.volume_Icc] at hh
  exact (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top).mp hh.le
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma expansion_almost_conull {ι : Type*} {F D : ι → ℝ → ℝ}
    {K : ℝ≥0} {e U L : ℝ} {A : Set ℝ}
    (hd : ∀ j x, HasDerivAt (F j) (D j x) x)
    (hp : ∀ j x, (1/2 : ℝ) ≤ D j x) (hup : ∀ j x, D j x ≤ U)
    (hK : ∀ j, LipschitzWith K (D j)) (hlarge : ∀ x, ∃ j, 1+e ≤ D j x)
    (he : 0 < e) (hKL : (K : ℝ)*L ≤ e) (hU : 0 < U) (hL : 0 < L)
    (hinv : ∀ j, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ F j x ∈ A)
    (hA : MeasurableSet A) (hpos : volume A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, L ≤ b-a ∧ volume (Icc a b \ A) ≤ ENNReal.ofReal ε := by
  let C := Real.exp (4*(K : ℝ)*U*L/e)*U*L
  have hC : 0 < C := mul_pos (mul_pos (Real.exp_pos _) hU) hL
  obtain ⟨a,b,hab,hsmall,hdef⟩ := exists_density_interval hA hpos hL (div_pos hε hC)
  obtain ⟨a',b',hl,_,hbound⟩ := expanding_interval_defect hd hp hup hK hlarge he hKL hU.le hinv hab hsmall
  refine ⟨a',b',hl,hbound.trans ?_⟩
  change ENNReal.ofReal (C/(b-a))*volume (Icc a b \ A) ≤ ENNReal.ofReal ε
  calc
    _ ≤ ENNReal.ofReal (C/(b-a))*(ENNReal.ofReal (ε/C)*ENNReal.ofReal (b-a)) :=
      mul_le_mul_right hdef _
    _ = ENNReal.ofReal ((C/(b-a))*((ε/C)*(b-a))) := by
      rw [← ENNReal.ofReal_mul (div_pos hε hC).le,← ENNReal.ofReal_mul (div_pos hC (sub_pos.mpr hab)).le]
    _ = ENNReal.ofReal ε := by congr 1; field_simp [hC.ne', (sub_pos.mpr hab).ne']
lemma expansion_conull_interval {ι : Type*} {F D : ι → ℝ → ℝ}
    {K : ℝ≥0} {e U L P : ℝ} {A : Set ℝ}
    (hd : ∀ j x, HasDerivAt (F j) (D j x) x)
    (hp : ∀ j x, (1/2 : ℝ) ≤ D j x) (hup : ∀ j x, D j x ≤ U)
    (hK : ∀ j, LipschitzWith K (D j)) (hlarge : ∀ x, ∃ j, 1+e ≤ D j x)
    (he : 0 < e) (hKL : (K : ℝ)*L ≤ e) (hU : 0 < U) (hL : 0 < L) (hP : 0 < P)
    (hinv : ∀ j, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ F j x ∈ A)
    (hA : MeasurableSet A) (hpos : volume A ≠ 0)
    (hper : ∀ (n : ℤ) x, x+(n : ℝ)*P ∈ A ↔ x ∈ A) :
    ∃ a b : ℝ, b-a=L/2 ∧ volume (Icc a b \ A)=0 := by
  have hex : ∀ n : ℕ, ∃ a b : ℝ, a ∈ Icc 0 P ∧ L ≤ b-a ∧
      volume (Icc a b \ A) ≤ ENNReal.ofReal (1/((n : ℝ)+1)) := by
    intro n
    obtain ⟨a,b,hl,hdef⟩ := expansion_almost_conull hd hp hup hK hlarge he hKL hU hL hinv hA hpos
      (by positivity : (0 : ℝ)<1/((n : ℝ)+1))
    obtain ⟨a',b',ha',hlen,hdef'⟩ := periodic_interval_normalize hP hper a b
    exact ⟨a',b',ha',by rwa [hlen],hdef'.trans_le hdef⟩
  choose a b ha hl hdef using hex
  apply compact_almost_conull_interval hL ha hl
  have ht : Tendsto (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht)
    (fun _ => zero_le) hdef
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma conull_extend_intervals {ι : Type*} {F : ι → ℝ → ℝ} {U : ℝ≥0}
    {e B a b : ℝ} {A : Set ℝ}
    (hLip : ∀ j, LipschitzWith U (F j)) (hmono : ∀ j, Monotone (F j))
    (hadvance : ∀ x, ∃ j, x+e ≤ F j x) (hdispl : ∀ j x, F j x ≤ x+B)
    (he : 0 < e) (hab : a ≤ b) (hB : B ≤ b-a)
    (hinv : ∀ j, ∀ᵐ x : ℝ ∂volume, x ∈ A ↔ F j x ∈ A)
    (hnull : volume (Icc a b \ A)=0) (n : ℕ) :
    ∃ b' : ℝ, b+(n : ℝ)*e ≤ b' ∧ volume (Icc a b' \ A)=0 := by
  induction n with
  | zero => exact ⟨b,by simp,hnull⟩
  | succ n ih =>
    obtain ⟨b',hb',hnull'⟩ := ih
    obtain ⟨j,hj⟩ := hadvance b'
    have hb : b ≤ b' := le_trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) he.le)) hb'
    have hfa : F j a ≤ b' := (hdispl j a).trans (by linarith)
    have himage : volume (Icc (F j a) (F j b') \ A)=0 := by
      apply le_antisymm _ bot_le
      exact (interval_defect_image_bound (hab.trans hb) (hLip j).continuous.continuousOn
        ((hmono j).monotoneOn _) (hLip j).lipschitzOnWith (hinv j)).trans (by simp [hnull'])
    refine ⟨F j b',?_,?_⟩
    · push_cast
      nlinarith
    · apply measure_mono_null (t := (Icc a b' \ A) ∪ (Icc (F j a) (F j b') \ A))
      · intro x hx
        by_cases hxb : x ≤ b'
        · exact Or.inl ⟨⟨hx.1.1,hxb⟩,hx.2⟩
        · exact Or.inr ⟨⟨le_trans hfa (le_of_not_ge hxb),hx.1.2⟩,hx.2⟩
      · exact le_antisymm ((measure_union_le _ _).trans (by rw [hnull',himage,add_zero])) bot_le
lemma conull_interval_alternation_false {A : Set ℝ} {a b κ : ℝ}
    (hκ : 0 < κ) (hab : κ < b-a) (hnull : volume (Icc a b \ A)=0)
    (halt : ∀ᵐ x : ℝ ∂volume, x+κ ∈ A ↔ x ∉ A) : False := by
  have hmem : ∀ᵐ x : ℝ ∂volume, x ∈ Icc a b → x ∈ A := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => by
      simp only [Classical.not_imp] at hx
      exact hx) hnull
  have hmem' := (measurePreserving_add_right volume κ).quasiMeasurePreserving.ae hmem
  have hbad : ∀ᵐ x : ℝ ∂volume, x ∉ Icc a (b-κ) := by
    filter_upwards [hmem,hmem',halt] with x hx hx' ha hxin
    have hxa : x ∈ A := hx ⟨hxin.1,by linarith [hxin.2]⟩
    have hxka : x+κ ∈ A := hx' ⟨by linarith [hxin.1],by linarith [hxin.2]⟩
    exact (ha.mp hxka) hxa
  have hz : volume (Icc a (b-κ))=0 := by
    have hh := ae_iff.mp hbad
    convert hh using 2
    ext x
    simp only [mem_Icc,mem_ofPred_eq,not_not]
  rw [Real.volume_Icc,ENNReal.ofReal_eq_zero] at hz
  linarith
end EuclideanFiveColor
end

end OAI
