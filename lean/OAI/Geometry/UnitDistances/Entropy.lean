import OAI.Geometry.UnitDistances.Information

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, p a * log (p a)

lemma atom_le_one {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (a : α) : p a ≤ 1 := by
  rw [← hs]
  exact single_le_sum (fun x _ => hp x) (mem_univ a)

lemma entropy_nonneg {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) : 0 ≤ entropy p := by
  unfold entropy
  apply neg_nonneg.mpr
  apply sum_nonpos
  intro a _
  exact mul_nonpos_of_nonneg_of_nonpos (hp a) (log_nonpos (hp a) (atom_le_one p hp hs a))

lemma entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    entropy p ≤ log (Fintype.card α) := by
  have hc : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  let q : α → ℝ := fun _ => (Fintype.card α : ℝ)⁻¹
  have hq : ∀ a, 0 ≤ q a := fun _ => inv_nonneg.mpr hc.le
  have hqs : ∑ a, q a = 1 := by simp [q, hc.ne']
  have hqz : ∀ a, q a ≠ 0 := fun _ => inv_ne_zero hc.ne'
  have hh := KL_nonneg p q hp hq hs hqs (fun a _ => hqz a)
  have hid : KL p q = -entropy p + log (Fintype.card α) := by
    unfold KL entropy
    have he (a : α) : p a * log (p a / q a) =
        p a * log (p a) + p a * log (Fintype.card α) := by
      by_cases hz : p a = 0
      · simp [hz]
      · rw [log_div hz (hqz a)]
        simp only [q, log_inv]
        ring
    simp_rw [he]
    rw [sum_add_distrib, ← sum_mul, hs]
    ring
  rw [hid] at hh
  linarith

lemma entropy_off_diagonal_bound [DecidableEq P] (w : P × P → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) {M : ℝ} (_hM : 0 < M)
    (hbound : ∀ p r, p ≠ r → w (p,r) ≤ M) :
    (1 - ∑ p, w (p,p)) * log (1/M) ≤ entropy w := by
  have he (x : P × P) : (if x.1 ≠ x.2 then w x else 0) * log (1/M) ≤
      -(w x * log (w x)) := by
    by_cases hd : x.1 = x.2
    · simp only [hd, ne_eq, not_true_eq_false, ite_false, zero_mul]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hw x)
        (log_nonpos (hw x) (atom_le_one w hw hs x)))
    · simp only [hd, ne_eq, not_false_eq_true, ite_true]
      by_cases hz : w x = 0
      · simp [hz]
      have hwp : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hz)
      have hl := log_le_log hwp (hbound x.1 x.2 hd)
      rw [one_div, log_inv]
      nlinarith [mul_le_mul_of_nonneg_left hl (hw x)]
  have hh := sum_le_sum (s := univ) (fun x _ => he x)
  rw [← sum_mul, sum_neg_distrib] at hh
  change (∑ x, if x.1 ≠ x.2 then w x else 0) * log (1/M) ≤ entropy w at hh
  have hsplit : (∑ x, if x.1 ≠ x.2 then w x else 0) = 1 - ∑ p, w (p,p) := by
    have he' (x : P × P) : (if x.1 ≠ x.2 then w x else 0) =
        w x - if x.1 = x.2 then w x else 0 := by split_ifs <;> simp_all
    simp_rw [he']
    rw [sum_sub_distrib, hs, Fintype.sum_prod_type]
    simp
  rwa [hsplit] at hh

lemma joint_KL_entropy (w : P × Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    KL w (fun x => (∑ q, w (x.1,q)) * (∑ p, w (p,x.2))) =
      entropy (fun p => ∑ q, w (p,q)) + entropy (fun q => ∑ p, w (p,q))
        - entropy w := by
  let a : P → ℝ := fun p => ∑ q, w (p,q)
  let b : Q → ℝ := fun q => ∑ p, w (p,q)
  have ha (x : P × Q) (hx : w x ≠ 0) : a x.1 ≠ 0 := by
    have hh := single_le_sum (s := univ) (f := fun q => w (x.1,q))
      (fun q _ => hw _) (mem_univ x.2)
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hw x) (Ne.symm hx)) hh)
  have hb (x : P × Q) (hx : w x ≠ 0) : b x.2 ≠ 0 := by
    have hh := single_le_sum (s := univ) (f := fun p => w (p,x.2))
      (fun p _ => hw _) (mem_univ x.1)
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hw x) (Ne.symm hx)) hh)
  have he (x : P × Q) : w x * log (w x / (a x.1*b x.2)) =
      w x * log (w x) - w x * log (a x.1) - w x * log (b x.2) := by
    by_cases hz : w x = 0
    · simp [hz]
    · rw [log_div hz (mul_ne_zero (ha x hz) (hb x hz)), log_mul (ha x hz) (hb x hz)]
      ring
  change (∑ x, w x * log (w x / (a x.1*b x.2))) = _
  simp_rw [he]
  rw [sum_sub_distrib, sum_sub_distrib]
  have h₁ : (∑ x : P × Q, w x * log (a x.1)) = ∑ p, a p * log (a p) := by
    rw [Fintype.sum_prod_type]
    simp_rw [← sum_mul]
    rfl
  have h₂ : (∑ x : P × Q, w x * log (b x.2)) = ∑ q, b q * log (b q) := by
    rw [Fintype.sum_prod_type, sum_comm]
    simp_rw [← sum_mul]
    rfl
  rw [h₁,h₂]
  dsimp [entropy, a, b]
  ring

theorem mutual_information_bound [DecidableEq P] [Nonempty P]
    (w : P × P → ℝ) (μ : P → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (hμ : ∀ p, 0 ≤ μ p) (hμs : ∑ p, μ p = 1)
    (hfst : ∀ p, ∑ r, w (p,r) = μ p) (hsnd : ∀ r, ∑ p, w (p,r) = μ r)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ p r, p ≠ r → w (p,r) ≤ M) :
    KL w (fun x => μ x.1*μ x.2) ≤
      2*log (Fintype.card P) - (1-∑ p, w (p,p))*log (1/M) := by
  have h₁ := entropy_le_log_card μ hμ hμs
  have h₂ := entropy_off_diagonal_bound w hw hs hM hbound
  have hid := joint_KL_entropy w hw
  simp only [hfst, hsnd] at hid
  rw [hid]
  linarith

noncomputable def indicator (E : P → Q → Prop) (p : P) (q : Q) : ℝ := by
  classical
  exact if E p q then 1 else 0
noncomputable def degree (E : P → Q → Prop) (q : Q) : ℝ := ∑ p, indicator E p q
noncomputable def edgeCount (E : P → Q → Prop) : ℝ := ∑ q, degree E q
noncomputable def wedge (E : P → Q → Prop) (x : P × P) : ℝ :=
  ∑ q, indicator E x.1 q * indicator E x.2 q / (edgeCount E * degree E q)
noncomputable def pointLaw (E : P → Q → Prop) (p : P) : ℝ :=
  (∑ q, indicator E p q) / edgeCount E

omit [Fintype P] [Fintype Q] in
lemma indicator_nonneg (E : P → Q → Prop) (p : P) (q : Q) : 0 ≤ indicator E p q := by
  classical
  unfold indicator
  split_ifs <;> norm_num

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

lemma edgeCount_nonneg (E : P → Q → Prop) : 0 ≤ edgeCount E :=
  sum_nonneg fun q _ => degree_nonneg E q

lemma wedge_nonneg (E : P → Q → Prop) (x : P × P) : 0 ≤ wedge E x := by
  unfold wedge
  exact sum_nonneg fun q _ => div_nonneg
    (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
    (mul_nonneg (edgeCount_nonneg E) (degree_nonneg E _))

lemma wedge_symm (E : P → Q → Prop) (p r : P) : wedge E (p,r) = wedge E (r,p) := by
  unfold wedge
  apply sum_congr rfl
  intro q _
  exact congrArg (fun a => a / (edgeCount E * degree E q)) (mul_comm _ _)

lemma pointLaw_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) : ∑ p, pointLaw E p = 1 := by
  unfold pointLaw
  rw [← sum_div, sum_comm]
  exact div_self hE

lemma wedge_fst (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (p : P) :
    ∑ r, wedge E (p,r) = pointLaw E p := by
  unfold wedge pointLaw
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [← sum_div, ← mul_sum]
  change indicator E p q * degree E q / (edgeCount E * degree E q) = _
  exact mul_div_mul_right _ _ (hd q)

lemma wedge_snd (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (r : P) :
    ∑ p, wedge E (p,r) = pointLaw E r := by
  simp_rw [wedge_symm E _ r]
  exact wedge_fst E hd r

lemma wedge_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) (hd : ∀ q, degree E q ≠ 0) :
    ∑ x, wedge E x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [wedge_fst E hd]
  exact pointLaw_sum E hE

theorem wedge_diagonal (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) :
    ∑ p, wedge E (p,p) = Fintype.card Q / edgeCount E := by
  classical
  unfold wedge
  rw [sum_comm]
  have he (q : Q) : (∑ p, indicator E p q * indicator E p q / (edgeCount E * degree E q)) =
      1 / edgeCount E := by
    have hi (p : P) : indicator E p q * indicator E p q = indicator E p q := by
      unfold indicator
      split_ifs <;> norm_num
    simp_rw [hi]
    rw [← sum_div]
    change degree E q / (edgeCount E * degree E q) = _
    simpa using mul_div_mul_right (1:ℝ) (edgeCount E) (hd q)
  simp_rw [he]
  simp [div_eq_mul_inv]

theorem wedge_atom (E : P → Q → Prop) {dmin : ℝ}
    (hE : 0 < edgeCount E) (hd : 0 < dmin) (hdeg : ∀ q, dmin ≤ degree E q)
    (hcodeg : ∀ p r, p ≠ r → (∑ q, indicator E p q * indicator E r q) ≤ 2)
    (p r : P) (hpr : p ≠ r) : wedge E (p,r) ≤ 2/(edgeCount E*dmin) := by
  unfold wedge
  calc
    _ ≤ ∑ q, indicator E p q * indicator E r q / (edgeCount E*dmin) := by
      apply sum_le_sum
      intro q _
      exact div_le_div_of_nonneg_left
        (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
        (mul_pos hE hd) (mul_le_mul_of_nonneg_left (hdeg q) hE.le)
    _ = (∑ q, indicator E p q * indicator E r q) / (edgeCount E*dmin) := by rw [sum_div]
    _ ≤ 2/(edgeCount E*dmin) := div_le_div_of_nonneg_right (hcodeg p r hpr) (by positivity)

theorem wedge_information [DecidableEq P] [Nonempty P]
    (E : P → Q → Prop) {dmin : ℝ} (hE : 0 < edgeCount E)
    (hd : 0 < dmin) (hdeg : ∀ q, dmin ≤ degree E q)
    (hcodeg : ∀ p r, p ≠ r → (∑ q, indicator E p q * indicator E r q) ≤ 2) :
    KL (wedge E) (fun x => pointLaw E x.1 * pointLaw E x.2) ≤
      2*log (Fintype.card P) - (1-Fintype.card Q/edgeCount E)*log (edgeCount E*dmin/2) := by
  have hdn : ∀ q, degree E q ≠ 0 := fun q => (lt_of_lt_of_le hd (hdeg q)).ne'
  have hh := mutual_information_bound (wedge E) (pointLaw E)
    (wedge_nonneg E) (wedge_sum E hE.ne' hdn)
    (fun p => div_nonneg (sum_nonneg fun q _ => indicator_nonneg E p q) hE.le)
    (pointLaw_sum E hE.ne') (wedge_fst E hdn) (wedge_snd E hdn)
    (show 0 < 2/(edgeCount E*dmin) by positivity) (wedge_atom E hE hd hdeg hcodeg)
  rw [wedge_diagonal E hdn] at hh
  convert hh using 1
  congr 2
  field_simp

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma center_linear (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (p-r)*conj q + (conj p-conj r)*q = p*conj p-r*conj r := by
  linear_combination hr-hp

noncomputable def centerPolynomial (p r : ℂ) : ℂ[X] :=
  (X-C p)*(C (p*conj p-r*conj r-(p-r)*conj p)-C (conj p-conj r)*X)-C (p-r)

lemma centerPolynomial_eval (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (centerPolynomial p r).eval q = 0 := by
  have hl := center_linear p r q hp hr
  simp only [centerPolynomial, eval_sub, eval_mul, eval_X, eval_C]
  linear_combination -(q-p)*hl+(p-r)*hp

lemma centerPolynomial_expansion (p r : ℂ) :
    centerPolynomial p r = C (-(conj p-conj r))*X^2+
      C (p*conj p-r*conj r-(p-r)*conj p+p*(conj p-conj r))*X+
      C (-(p*(p*conj p-r*conj r-(p-r)*conj p))-(p-r)) := by
  simp only [centerPolynomial, map_add, map_sub, map_neg, map_mul]
  ring

lemma centerPolynomial_ne_zero (p r : ℂ) (hpr : p ≠ r) : centerPolynomial p r ≠ 0 := by
  intro hz
  have hh := congrArg (fun f : ℂ[X] => f.coeff 2) hz
  rw [centerPolynomial_expansion] at hh
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_mul_X, coeff_C] at hh
  simp only [ite_true, ite_false, add_zero, coeff_zero] at hh
  exact hpr (star_injective (sub_eq_zero.mp (neg_eq_zero.mp hh)))

lemma centerPolynomial_degree (p r : ℂ) : (centerPolynomial p r).natDegree ≤ 2 := by
  rw [centerPolynomial_expansion]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow]; norm_num)
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X]; norm_num)
  · simp only [natDegree_C]; norm_num

theorem common_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, (q-p)*(conj q-conj p) = 1 ∧ (q-r)*(conj q-conj r) = 1) :
    S.card ≤ 2 := by
  have hh : S.card ≤ (centerPolynomial p r).natDegree :=
    Polynomial.card_le_degree_of_subset_roots ?_
  · exact hh.trans (centerPolynomial_degree p r)
  · intro q hq
    exact (Polynomial.mem_roots (centerPolynomial_ne_zero p r hpr)).mpr
      (centerPolynomial_eval p r q (hS q hq).1 (hS q hq).2)

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

theorem unit_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, dist p q = 1 ∧ dist r q = 1) : S.card ≤ 2 :=
  common_centers_card p r hpr S fun q hq =>
    ⟨unit_distance_equation p q (hS q hq).1, unit_distance_equation r q (hS q hq).2⟩

noncomputable def zCoordinate : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

lemma zCoordinate_apply (x : EuclideanSpace ℝ (Fin 2)) :
    zCoordinate x = x 0 + x 1 * Complex.I := rfl

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.IncidenceEntropy
open Finset UnitCodegree
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype P] in

theorem unit_incidence_codegree (E : P → Q → Prop) (x : P → ℂ) (y : Q → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hE : ∀ p q, E p q → dist (x p) (y q) = 1)
    (p r : P) (hpr : p ≠ r) : (∑ q, indicator E p q * indicator E r q) ≤ 2 := by
  classical
  let T : Finset Q := univ.filter fun q => E p q ∧ E r q
  have hs : (∑ q, indicator E p q * indicator E r q) = (T.card : ℝ) := by
    have hh (q : Q) : indicator E p q * indicator E r q =
        if E p q ∧ E r q then (1:ℝ) else 0 := by
      unfold indicator
      split_ifs <;> simp_all
    simp_rw [hh]
    simp [T]
  rw [hs]
  have hc := unit_centers_card (x p) (x r) (fun hh => hpr (hx hh)) (T.image y) ?_
  · rw [Finset.card_image_of_injective _ hy] at hc
    exact_mod_cast hc
  · intro q hq
    obtain ⟨s,hs,hsy⟩ := mem_image.mp hq
    have hss := (mem_filter.mp hs).2
    subst q
    exact ⟨hE p s hss.1,hE r s hss.2⟩

theorem planar_wedge_information [DecidableEq P] [Nonempty P]
    (E : P → Q → Prop) (x : P → EuclideanSpace ℝ (Fin 2))
    (y : Q → EuclideanSpace ℝ (Fin 2))
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hunit : ∀ p q, E p q → dist (x p) (y q) = 1)
    {dmin : ℝ} (hE : 0 < edgeCount E) (hd : 0 < dmin)
    (hdeg : ∀ q, dmin ≤ degree E q) :
    FiniteInformation.KL (wedge E) (fun t => pointLaw E t.1 * pointLaw E t.2) ≤
      2*Real.log (Fintype.card P) -
        (1-Fintype.card Q/edgeCount E)*Real.log (edgeCount E*dmin/2) := by
  apply wedge_information E hE hd hdeg
  apply unit_incidence_codegree E (fun p => zCoordinate (x p)) (fun q => zCoordinate (y q))
    (zCoordinate.injective.comp hx) (zCoordinate.injective.comp hy)
  intro p q hpq
  rw [LinearIsometryEquiv.dist_map]
  exact hunit p q hpq

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

def law (E : P → Q → Prop) (hE : 0<edgeCount E) : Law (P×Q) where
  val pq := indicator E pq.1 pq.2/edgeCount E
  nonneg pq := div_nonneg (indicator_nonneg E _ _) hE.le
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [←sum_div]
    rw [sum_comm]
    exact div_self hE.ne'

lemma right_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (q : Q) :
    (right (law E hE)).val q=degree E q/edgeCount E := by
  rw [right_val]
  simp only [law,←sum_div,degree]
lemma left_eq (E : P → Q → Prop) (hE : 0<edgeCount E) (p : P) :
    (left (law E hE)).val p=pointLaw E p := by
  rw [left_val]
  simp only [law,←sum_div,pointLaw]
lemma col_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {q : Q}
    (hq : 0<degree E q) (p : P) :
    (col (law E hE) q).val p=indicator E p q/degree E q := by
  rw [col_val (law E hE) (by rw [right_eq]; exact div_pos hq hE),right_eq]
  change (indicator E p q/edgeCount E)/(degree E q/edgeCount E)=_
  field_simp
lemma row_eq (E : P → Q → Prop) (hE : 0<edgeCount E) {p : P}
    (hp : 0<∑q,indicator E p q) (q : Q) :
    (row (law E hE) p).val q=indicator E p q/(∑q,indicator E p q) := by
  rw [row_val (law E hE) (by rw [left_eq]; exact div_pos hp hE),left_eq]
  change (indicator E p q/edgeCount E)/((∑q,indicator E p q)/edgeCount E)=_
  field_simp

lemma wedge_val (E : P → Q → Prop) (hE : 0<edgeCount E)
    (hd : ∀q,0<degree E q) (a : Q×(P×P)) :
    (WedgeLaw.law (law E hE)).val a=
      indicator E a.2.1 a.1*indicator E a.2.2 a.1/(edgeCount E*degree E a.1) := by
  change (right (law E hE)).val a.1*((col (law E hE) a.1).val a.2.1*(col (law E hE) a.1).val a.2.2)=_
  rw [right_eq,col_eq _ _ (hd _),col_eq _ _ (hd _)]
  field_simp

theorem edge_count (E : P → Q → Prop) (hE : 0<edgeCount E)
    {d : ℝ} (hd : 0<d) (hdeg : ∀q,d≤degree E q)
    (hcodeg : ∀p r,p≠r → (∑q,indicator E p q*indicator E r q)≤2)
    (A : Q×(P×P) → Prop) (hA : ∀a,A a → a.2.1≠a.2.2) :
    event (WedgeLaw.law (law E hE)) A ≤
      ((univ.filter (fun pr : P×P => ∃q,A (q,pr))).card:ℝ)*2/(edgeCount E*d) := by
  have hg : ∀q,0<degree E q := fun q => hd.trans_le (hdeg q)
  let B := univ.filter (fun pr : P×P => ∃q,A (q,pr))
  calc
    _ ≤ ∑pr∈B,IncidenceEntropy.wedge E pr := by
      unfold event avg
      rw [Fintype.sum_prod_type,sum_comm]
      dsimp only [B]
      simp only [sum_filter]
      apply sum_le_sum
      intro pr _
      by_cases hb : ∃q,A (q,pr)
      · simp only [hb,↓reduceIte]
        unfold IncidenceEntropy.wedge
        apply sum_le_sum
        intro q _
        rw [wedge_val E hE hg]
        split_ifs
        · simp only [mul_one]
          exact le_rfl
        · simp only [mul_zero]
          exact div_nonneg (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
            (mul_nonneg hE.le (degree_nonneg E _))
      · simp only [hb,↓reduceIte]
        apply le_of_eq
        apply sum_eq_zero
        intro q _
        simp [show ¬A (q,pr) from fun h => hb ⟨q,h⟩]
    _ ≤ (B.card:ℝ)*(2/(edgeCount E*d)) := by
      calc
        _ ≤ ∑pr∈B,2/(edgeCount E*d) := by
          apply sum_le_sum
          intro pr hpr
          obtain ⟨q,hq⟩ := (mem_filter.mp hpr).2
          exact wedge_atom E hE hd hdeg hcodeg pr.1 pr.2 (hA (q,pr) hq)
        _ = _ := by simp
    _ = _ := by ring
end
end PlanarUnitDistances.UniformGraphLaw

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def E (P Q : Finset Plane) (p : P) (q : Q) : Prop := dist (p:Plane) (q:Plane)=1
lemma degree_eq (P Q : Finset Plane) (q : Q) :
    IncidenceEntropy.degree (E P Q) q=CircleIncidence.degree P q := by
  rw [CircleIncidence.degree_sum]
  exact Finset.sum_coe_sort P (fun p => if dist p (q:Plane)=1 then (1:ℝ) else 0)
lemma edgeCount_eq (P Q : Finset Plane) :
    IncidenceEntropy.edgeCount (E P Q)=CircleIncidence.incidences P Q := by
  simp only [IncidenceEntropy.edgeCount,degree_eq,Finset.sum_coe_sort,CircleIncidence.incidences]
lemma row_count (P Q : Finset Plane) (p : P) :
    (∑q,IncidenceEntropy.indicator (E P Q) p q)=CircleIncidence.degree Q p := by
  change (∑q : Q,if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)=_
  rw [CircleIncidence.degree_sum]
  exact (Finset.sum_coe_sort Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)).trans
    (by simp only [dist_comm])
lemma card_pos (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) :
    0<P.card ∧ 0<Q.card := by
  have h := he.trans_le (CircleIncidence.incidences_le P Q)
  have hP : (0:ℝ)<P.card := pos_of_mul_pos_left h (Nat.cast_nonneg _)
  have hQ : (0:ℝ)<Q.card := pos_of_mul_pos_right h (Nat.cast_nonneg _)
  exact ⟨Nat.cast_pos.mp hP,Nat.cast_pos.mp hQ⟩
def graph (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) : Law (P×Q) :=
  UniformGraphLaw.law (E P Q) (by rw [edgeCount_eq]; exact he)
lemma left_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) :
    (left (graph P Q he)).val p=CircleIncidence.degree Q p/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.left_eq,IncidenceEntropy.pointLaw,edgeCount_eq,row_count]
lemma right_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (q : Q) :
    (right (graph P Q he)).val q=CircleIncidence.degree P q/CircleIncidence.incidences P Q := by
  rw [graph,UniformGraphLaw.right_eq,degree_eq,edgeCount_eq]
lemma row_le (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) (p : P) (q : Q)
    (hp : 0<CircleIncidence.degree Q p) :
    (row (graph P Q he) p).val q ≤ 1/CircleIncidence.degree Q p := by
  rw [graph,UniformGraphLaw.row_eq _ _ (by rw [row_count]; exact hp),row_count]
  apply div_le_div_of_nonneg_right _ hp.le
  unfold IncidenceEntropy.indicator
  split_ifs <;> norm_num

def counting (P : Finset Plane) (hp : 0<P.card) : Law P where
  val _ := 1/(P.card:ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt hp]
lemma counting_event (P : Finset Plane) (hp : 0<P.card) (A : Finset P) :
    event (counting P hp) (fun p => p∈A)=(A.card:ℝ)/(P.card:ℝ) := by
  have hattach : P.attach ∩ A=A := by ext p; simp
  simp [event,avg,counting,mul_ite,Finset.sum_ite_mem,hattach,div_eq_mul_inv]

def image {P : Finset Plane} (A : Finset P) : Finset Plane := A.image Subtype.val
lemma image_sub {P : Finset Plane} (A : Finset P) : image A⊆P := by
  intro p hp
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
  exact a.property
lemma image_card {P : Finset Plane} (A : Finset P) : (image A).card=A.card :=
  Finset.card_image_of_injective _ Subtype.val_injective
lemma event_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    (A : Finset P) (B : Finset Q) :
    event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B)=
      CircleIncidence.incidences (image A) (image B)/CircleIncidence.incidences P Q := by
  simp only [event,avg,graph,UniformGraphLaw.law,edgeCount_eq,Fintype.sum_prod_type]
  simp_rw [mul_ite,mul_one,mul_zero,ite_and]
  have hattach : Q.attach ∩ B=B := by ext q; simp
  have hsum : ∀p : P,
      (∑q : Q,if p∈A then if q∈B then IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 else 0)=
      if p∈A then ∑q∈B,IncidenceEntropy.indicator (E P Q) p q/CircleIncidence.incidences P Q else 0 := by
    intro p
    by_cases hp : p∈A
    · simp [hp,hattach]
    · simp [hp]
  simp_rw [hsum]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  simp_rw [←Finset.sum_div]
  rw [Finset.sum_comm]
  congr 1
  unfold CircleIncidence.incidences image
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  apply Finset.sum_congr rfl
  intro q _
  rw [CircleIncidence.degree_sum,Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
  rfl

theorem expansion (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    {ξ : ℝ}
    (hx : ∀A⊆P,∀B⊆Q,CircleIncidence.incidences A B/CircleIncidence.incidences P Q ≤
      Real.sqrt ((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))*
        (((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))^(1/25:ℝ)+ξ)) :
    ∀A : Finset P,∀B : Finset Q,event (graph P Q he) (fun pq => pq.1∈A ∧ pq.2∈B) ≤
      Real.sqrt (event (counting P (card_pos P Q he).1) (fun p => p∈A)*
        event (counting Q (card_pos P Q he).2) (fun q => q∈B))*
        ((event (counting P (card_pos P Q he).1) (fun p => p∈A)*
          event (counting Q (card_pos P Q he).2) (fun q => q∈B))^(1/25:ℝ)+ξ) := by
  intro A B
  rw [event_eq,counting_event,counting_event]
  simpa only [image_card] using hx (image A) (image_sub A) (image B) (image_sub B)

lemma wedge_eq (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    (hd : ∀q : Q,0<CircleIncidence.degree P q) :
    FiniteInformation.wedge (right (graph P Q he)).val (fun q => (col (graph P Q he) q).val)=
      IncidenceEntropy.wedge (E P Q) := by
  funext pr
  unfold FiniteInformation.wedge IncidenceEntropy.wedge
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  rw [graph,UniformGraphLaw.right_eq]
  simp only [UniformGraphLaw.col_eq _ _ (by rw [degree_eq]; exact hd q)]
  have hq : IncidenceEntropy.degree (E P Q) q≠0 := by rw [degree_eq]; exact (hd q).ne'
  field_simp

theorem information (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q)
    {d : ℝ} (hd : 0<d) (hdeg : ∀q : Q,d≤CircleIncidence.degree P q) :
    FiniteInformation.KL
      (FiniteInformation.wedge (right (graph P Q he)).val (fun q => (col (graph P Q he) q).val))
      (fun pr => (left (graph P Q he)).val pr.1*(left (graph P Q he)).val pr.2) ≤
      2*Real.log (P.card:ℝ)-(1-(Q.card:ℝ)/CircleIncidence.incidences P Q)*
        Real.log (CircleIncidence.incidences P Q*d/2) := by
  have : Nonempty P := (Finset.card_pos.mp (card_pos P Q he).1).to_subtype
  have hge : 0<IncidenceEntropy.edgeCount (E P Q) := by rw [edgeCount_eq]; exact he
  have hh := IncidenceEntropy.planar_wedge_information (E P Q) (fun p => (p:Plane)) (fun q => (q:Plane))
    Subtype.val_injective Subtype.val_injective (fun _ _ h => h) hge hd (fun q => by rw [degree_eq]; exact hdeg q)
  rw [wedge_eq P Q he (fun q => hd.trans_le (hdeg q))]
  simp only [graph,UniformGraphLaw.left_eq]
  simpa only [Fintype.card_coe,edgeCount_eq] using hh
end
end PlanarUnitDistances.GeometricLaw

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f : ι → ℝ} {a : ℝ}
lemma Upper.log_ratio (hf : Upper F t f a) (hfp : ∀ᶠi in F,0<f i)
    (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠi in F,Real.log (f i)/Real.log (t i)≤a+ε := by
  filter_upwards [hf ε hε,hfp,ht.eventually_gt_atTop 1] with i hi hfi hti
  apply (div_le_iff₀ (Real.log_pos hti)).mpr
  have hh := Real.log_le_log hfi hi
  simpa only [Real.log_rpow (zero_lt_one.trans hti)] using hh
lemma Lower.log_ratio (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠi in F,a-ε≤Real.log (f i)/Real.log (t i) := by
  filter_upwards [hf ε hε,ht.eventually_gt_atTop 1] with i hi hti
  apply (le_div_iff₀ (Real.log_pos hti)).mpr
  have hh := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hti) _) hi
  simpa only [Real.log_rpow (zero_lt_one.trans hti)] using hh
end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.InformationPowers
open Filter PowerGrowth

theorem information_rate {t m n e D : ℕ → ℝ} {M N E γ : ℝ}
    (ht : Tendsto t atTop atTop) (hγ : 0<γ)
    (hm : Upper atTop t m M) (hn : Upper atTop t n N) (he : Lower atTop t e E)
    (hm0 : ∀ᶠi : ℕ in atTop,(0:ℝ) < m i) (hn0 : ∀ᶠi : ℕ in atTop,(0:ℝ) < n i)
    (hNE : N<E) (hV : 0<2*E-N)
    (hD : ∀ᶠi in atTop,D i≤2*Real.log (m i)-
      (1-n i/e i)*Real.log (e i*(γ*e i/n i)/2)) :
    ∀ε : ℝ,0<ε → ∀ᶠi in atTop,D i/Real.log (t i)≤2*M-2*E+N+ε := by
  let V := 2*E-N
  have he0 := he.eventually_pos ht
  have hr := hn.ratio_zero he (hn0.mono fun _ hi => hi.le) ht hNE
  have hprod : Lower atTop t (fun i => e i*(γ*e i/n i)/2) V := by
    have hh := (he.mul (he.div hn hn0 ht) ht).const_mul ht (show 0<γ/2 by positivity)
    change Lower atTop t _ (2*E-N)
    convert hh using 1
    · ext i; ring
    · ring
  intro ε hε
  let δ := min (ε/4) (V/2)
  have hδ : 0<δ := lt_min (by positivity) (by dsimp [V]; positivity)
  have hδV : δ≤V/2 := min_le_right _ _
  have hδε : δ≤ε/4 := min_le_left _ _
  have hrv : 0<ε/(4*V) := by dsimp [V]; positivity
  filter_upwards [hD,hm.log_ratio hm0 ht (show 0<ε/8 by positivity),hprod.log_ratio ht hδ,
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),hr.eventually_le_const hrv,hn0,he0,
    ht.eventually_gt_atTop 1] with i hDi hMi hVi hr1 hrε hni hei hti
  have hl : 0<Real.log (t i) := Real.log_pos hti
  have hr0 : 0≤n i/e i := div_nonneg hni.le hei.le
  have hrV : n i/e i*V≤ε/4 := by
    have hh := (le_div_iff₀ (show 0<4*V by positivity)).mp hrε
    nlinarith
  have hmult := mul_le_mul_of_nonneg_left hVi (show 0≤1-n i/e i by linarith)
  have hdivide := (div_le_div_of_nonneg_right hDi hl.le)
  rw [sub_div,mul_div_assoc,mul_div_assoc] at hdivide
  have hout : D i/Real.log (t i)≤2*M-V+ε := by
    nlinarith [mul_nonneg hr0 hδ.le]
  dsimp only [V] at hout
  convert hout using 1; ring
end PlanarUnitDistances.InformationPowers

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f : ι → ℝ} {a b : ℝ}
lemma Upper.power_bound (hf : Upper F t f a) (hab : a < b) :
    ∀ᶠi in F,f i ≤ t i^b := by
  convert hf (b-a) (sub_pos.mpr hab) using 1; ring_nf
lemma Lower.power_bound (hf : Lower F t f a) (hab : b < a) :
    ∀ᶠi in F,t i^b ≤ f i := by
  simpa only [sub_sub_cancel] using hf (a-b) (sub_pos.mpr hab)
lemma Lower.tends_to_infinity (hf : Lower F t f a) (ht : Tendsto t F atTop) (ha : 0 < a) :
    Tendsto f F atTop := by
  exact tendsto_atTop_mono' F (hf.power_bound (by linarith : a/2 < a))
    ((_root_.tendsto_rpow_atTop (by positivity : 0 < a/2)).comp ht)
end PlanarUnitDistances.PowerGrowth

end OAI
