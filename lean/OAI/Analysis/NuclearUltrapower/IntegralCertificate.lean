import OAI.Analysis.NuclearUltrapower.SOSGap
import OAI.Analysis.NuclearUltrapower.SOSCertificate

namespace OAI

section

namespace NuclearUltrapower.SL3Certificate
variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem dot_nil_left (r : List ℤ) : dot [] r = 0 := by cases r <;> rfl
@[simp] theorem dot_nil_right (q : List ℤ) : dot q [] = 0 := by cases q <;> rfl

theorem dot_eq_sum_getD (N : ℕ) (q r : List ℤ) (hq : q.length ≤ N) (hr : r.length ≤ N) :
    dot q r = ∑ k ∈ Finset.range N, q.getD k 0 * r.getD k 0 := by
  induction N generalizing q r with
  | zero =>
    have hq' : q = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hq)
    have hr' : r = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hr)
    simp [hq', hr']
  | succ N ih =>
    cases q with
    | nil => simp
    | cons a q =>
      cases r with
      | nil => simp
      | cons b r =>
        rw [dot, ih q r (by simpa using hq) (by simpa using hr), Finset.sum_range_succ']
        simp [add_comm]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_list_sum (v : List A) : star v.sum = (v.map star).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih]

omit [StarRing A] [PartialOrder A] [StarOrderedRing A] in
theorem list_sum_finset {ι J : Type*} (v : List ι) (s : Finset J) (f : ι → J → A) :
    (v.map (fun i => ∑ k ∈ s, f i k)).sum = ∑ k ∈ s, (v.map (fun i => f i k)).sum := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih, Finset.sum_add_distrib]

omit [PartialOrder A] [StarOrderedRing A] in
theorem list_gram_identity (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      ∑ k ∈ Finset.range N,
        star ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) *
          ((v.map (fun p => (p.2.getD k 0) • p.1)).sum) := by
  have hm (n m : ℤ) (x y : A) : (n*m) • (x*y) = (n • x) * (m • y) := by
    simp only [zsmul_eq_mul, Int.cast_mul, mul_assoc]
    rw [← mul_assoc x (m : A) y, ← (Int.cast_commute m x).eq, mul_assoc]
  have hdot : (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum =
      (v.map (fun p => (v.map (fun q =>
        ∑ k ∈ Finset.range N, (p.2.getD k 0 • star p.1) * (q.2.getD k 0 • q.1))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [dot_eq_sum_getD N _ _ (h p hp) (h q hq), Finset.sum_smul]
    simp only [hm]
  rw [hdot]
  simp only [list_sum_finset]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.sum_map_mul_left, List.sum_map_mul_right, star_list_sum,
    List.map_map, Function.comp_def, star_zsmul]

theorem list_gram_nonneg (N : ℕ) (v : List (A × List ℤ))
    (h : ∀ p ∈ v, p.2.length ≤ N) :
    0 ≤ (v.map (fun p => (v.map (fun q => dot p.2 q.2 • (star p.1 * q.1))).sum)).sum := by
  rw [list_gram_identity N v h]
  exact Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
end NuclearUltrapower.SL3Certificate
end

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate
def gramData : List (List ℤ) := [gramRow0, gramRow1, gramRow2, gramRow3, gramRow4, gramRow5, gramRow6, gramRow7, gramRow8, gramRow9, gramRow10, gramRow11, gramRow12, gramRow13, gramRow14, gramRow15, gramRow16, gramRow17, gramRow18, gramRow19, gramRow20, gramRow21, gramRow22, gramRow23, gramRow24, gramRow25, gramRow26, gramRow27, gramRow28, gramRow29, gramRow30, gramRow31, gramRow32, gramRow33, gramRow34, gramRow35, gramRow36, gramRow37, gramRow38, gramRow39, gramRow40, gramRow41, gramRow42, gramRow43, gramRow44, gramRow45, gramRow46, gramRow47, gramRow48, gramRow49, gramRow50, gramRow51, gramRow52, gramRow53, gramRow54, gramRow55, gramRow56, gramRow57, gramRow58, gramRow59, gramRow60, gramRow61, gramRow62, gramRow63, gramRow64, gramRow65, gramRow66, gramRow67, gramRow68, gramRow69, gramRow70, gramRow71, gramRow72, gramRow73, gramRow74, gramRow75, gramRow76, gramRow77, gramRow78, gramRow79, gramRow80, gramRow81, gramRow82, gramRow83, gramRow84, gramRow85, gramRow86, gramRow87, gramRow88, gramRow89, gramRow90, gramRow91, gramRow92, gramRow93, gramRow94, gramRow95, gramRow96, gramRow97, gramRow98, gramRow99, gramRow100, gramRow101, gramRow102, gramRow103, gramRow104, gramRow105, gramRow106, gramRow107, gramRow108, gramRow109, gramRow110, gramRow111, gramRow112, gramRow113, gramRow114, gramRow115, gramRow116, gramRow117, gramRow118, gramRow119, gramRow120]
theorem gramData_eq : gramData = SL3Certificate.gram := by rfl
theorem gramData_roots : gramData = columns.map (fun q => columns.map (dot q)) := by
  rw [gramData_eq]
  change _ = [columns.map (dot q0), columns.map (dot q1), columns.map (dot q2), columns.map (dot q3), columns.map (dot q4), columns.map (dot q5), columns.map (dot q6), columns.map (dot q7), columns.map (dot q8), columns.map (dot q9), columns.map (dot q10), columns.map (dot q11), columns.map (dot q12), columns.map (dot q13), columns.map (dot q14), columns.map (dot q15), columns.map (dot q16), columns.map (dot q17), columns.map (dot q18), columns.map (dot q19), columns.map (dot q20), columns.map (dot q21), columns.map (dot q22), columns.map (dot q23), columns.map (dot q24), columns.map (dot q25), columns.map (dot q26), columns.map (dot q27), columns.map (dot q28), columns.map (dot q29), columns.map (dot q30), columns.map (dot q31), columns.map (dot q32), columns.map (dot q33), columns.map (dot q34), columns.map (dot q35), columns.map (dot q36), columns.map (dot q37), columns.map (dot q38), columns.map (dot q39), columns.map (dot q40), columns.map (dot q41), columns.map (dot q42), columns.map (dot q43), columns.map (dot q44), columns.map (dot q45), columns.map (dot q46), columns.map (dot q47), columns.map (dot q48), columns.map (dot q49), columns.map (dot q50), columns.map (dot q51), columns.map (dot q52), columns.map (dot q53), columns.map (dot q54), columns.map (dot q55), columns.map (dot q56), columns.map (dot q57), columns.map (dot q58), columns.map (dot q59), columns.map (dot q60), columns.map (dot q61), columns.map (dot q62), columns.map (dot q63), columns.map (dot q64), columns.map (dot q65), columns.map (dot q66), columns.map (dot q67), columns.map (dot q68), columns.map (dot q69), columns.map (dot q70), columns.map (dot q71), columns.map (dot q72), columns.map (dot q73), columns.map (dot q74), columns.map (dot q75), columns.map (dot q76), columns.map (dot q77), columns.map (dot q78), columns.map (dot q79), columns.map (dot q80), columns.map (dot q81), columns.map (dot q82), columns.map (dot q83), columns.map (dot q84), columns.map (dot q85), columns.map (dot q86), columns.map (dot q87), columns.map (dot q88), columns.map (dot q89), columns.map (dot q90), columns.map (dot q91), columns.map (dot q92), columns.map (dot q93), columns.map (dot q94), columns.map (dot q95), columns.map (dot q96), columns.map (dot q97), columns.map (dot q98), columns.map (dot q99), columns.map (dot q100), columns.map (dot q101), columns.map (dot q102), columns.map (dot q103), columns.map (dot q104), columns.map (dot q105), columns.map (dot q106), columns.map (dot q107), columns.map (dot q108), columns.map (dot q109), columns.map (dot q110), columns.map (dot q111), columns.map (dot q112), columns.map (dot q113), columns.map (dot q114), columns.map (dot q115), columns.map (dot q116), columns.map (dot q117), columns.map (dot q118), columns.map (dot q119), columns.map (dot q120)]
  rw [gram_row_0, gram_row_1, gram_row_2, gram_row_3, gram_row_4, gram_row_5, gram_row_6, gram_row_7, gram_row_8, gram_row_9, gram_row_10, gram_row_11, gram_row_12, gram_row_13, gram_row_14, gram_row_15, gram_row_16, gram_row_17, gram_row_18, gram_row_19, gram_row_20, gram_row_21, gram_row_22, gram_row_23, gram_row_24, gram_row_25, gram_row_26, gram_row_27, gram_row_28, gram_row_29, gram_row_30, gram_row_31, gram_row_32, gram_row_33, gram_row_34, gram_row_35, gram_row_36, gram_row_37, gram_row_38, gram_row_39, gram_row_40, gram_row_41, gram_row_42, gram_row_43, gram_row_44, gram_row_45, gram_row_46, gram_row_47, gram_row_48, gram_row_49, gram_row_50, gram_row_51, gram_row_52, gram_row_53, gram_row_54, gram_row_55, gram_row_56, gram_row_57, gram_row_58, gram_row_59, gram_row_60, gram_row_61, gram_row_62, gram_row_63, gram_row_64, gram_row_65, gram_row_66, gram_row_67, gram_row_68, gram_row_69, gram_row_70, gram_row_71, gram_row_72, gram_row_73, gram_row_74, gram_row_75, gram_row_76, gram_row_77, gram_row_78, gram_row_79, gram_row_80, gram_row_81, gram_row_82, gram_row_83, gram_row_84, gram_row_85, gram_row_86, gram_row_87, gram_row_88, gram_row_89, gram_row_90, gram_row_91, gram_row_92, gram_row_93, gram_row_94, gram_row_95, gram_row_96, gram_row_97, gram_row_98, gram_row_99, gram_row_100, gram_row_101, gram_row_102, gram_row_103, gram_row_104, gram_row_105, gram_row_106, gram_row_107, gram_row_108, gram_row_109, gram_row_110, gram_row_111, gram_row_112, gram_row_113, gram_row_114, gram_row_115, gram_row_116, gram_row_117, gram_row_118, gram_row_119, gram_row_120]
  rfl

def gramPolyRow (a : Mat3) (r : List ℤ) : Poly Mat3 :=
  (basis.zip r).map (fun q => (matMul (matInv a) q.1, -10*q.2))

theorem residualRows_decomp : residualRows = residualRow0 :: residualRow1 ::
    (basis.zip gramData).map (fun p => gramPolyRow p.1 p.2) := by rfl

def rootPairs : List (Mat3 × List ℤ) := basis.zip columns

theorem columns_length : columns.map List.length = List.replicate 121 120 := by decide +kernel

theorem columns_bound : ∀ q ∈ columns, q.length ≤ 120 := by
  intro q hq
  have h := List.mem_map_of_mem (f := List.length) hq
  rw [columns_length] at h
  have : q.length = 120 := (List.mem_replicate.mp h).2
  omega

section Operator
variable {A : Type*} [Ring A] [StarRing A]

def gramValue (f : Mat3 → A) : A :=
  (rootPairs.map (fun p =>
    (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum)).sum

theorem gramValue_nonneg [PartialOrder A] [StarOrderedRing A] (f : Mat3 → A) :
    0 ≤ gramValue f := by
  have h := list_gram_nonneg 120
    (rootPairs.map (fun p => (f p.1, p.2))) (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact columns_bound q.2 (List.of_mem_zip hq).2)
  simpa only [gramValue, List.map_map, Function.comp_def] using h

theorem eval_gram_rows (f : Mat3 → A)
    (hf : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f ((basis.zip gramData).flatMap (fun p => gramPolyRow p.1 p.2)) =
      (-10 : ℤ) • gramValue f := by
  rw [gramData_roots]
  simp only [List.zip_map_right, List.flatMap_map, Prod.map, id_eq,
    Function.comp_def, gramPolyRow, List.map_map]
  rw [eval_flatMap]
  have hrow (p : Mat3 × List ℤ) (hp : p ∈ rootPairs) :
      eval f ((basis.zip columns).map (fun q =>
        (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))) =
        (-10 : ℤ) • (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum := by
    simp only [eval, List.map_map, Function.comp_def, mul_smul, List.smul_sum,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hf p.1 (List.of_mem_zip hp).1 q.1 (List.of_mem_zip hq).1]
  change (rootPairs.map (fun p => eval f ((basis.zip columns).map
    (fun q => (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))))).sum = _
  rw [List.map_congr_left hrow]
  simp only [gramValue, List.smul_sum, List.map_map, Function.comp_def]

end Operator
end NuclearUltrapower.SOS
end

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_getD_flatten {a : α} (rs : List (List α)) (n : ℕ) (h : a ∈ rs.getD n []) :
    a ∈ rs.flatten := by
  induction rs generalizing n with
  | nil => simp at h
  | cons r rs ih =>
    cases n with
    | zero => exact List.mem_append_left _ (by simpa using h)
    | succ n => exact List.mem_append_right _ (ih n (by simpa using h))

theorem bucket_support_original (le : α → α → Bool)
    (original : List (Poly α)) (buckets : List (List (Poly α)))
    (hnorm : original.map (normalize le) = buckets.map (fun r => normalize le r.flatten))
    (b : ℕ) {m : α}
    (hm : m ∈ (normalize le (buckets.flatMap (fun r => r.getD b []))).map Prod.fst) :
    m ∈ original.flatten.map Prod.fst := by
  have hm' := (support_normalize_iff le _ m).mp hm
  obtain ⟨p, hp, hpval⟩ := List.mem_map.mp hm'
  obtain ⟨r, hr, hpr⟩ := List.mem_flatMap.mp hp
  have hpr' : p ∈ r.flatten := mem_getD_flatten r b hpr
  have hn : normalize le r.flatten ∈ original.map (normalize le) := by
    rw [hnorm]
    exact List.mem_map_of_mem hr
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hn
  have hmnorm : m ∈ (normalize le r.flatten).map Prod.fst :=
    (support_normalize_iff le _ m).mpr (List.mem_map.mpr ⟨p,hpr',hpval⟩)
  rw [← heq] at hmnorm
  have hmq := (support_normalize_iff le q m).mp hmnorm
  obtain ⟨t, ht, htval⟩ := List.mem_map.mp hmq
  exact List.mem_map.mpr ⟨t, List.mem_flatten.mpr ⟨q,hq,ht⟩, htval⟩
end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS

theorem delta_good {p : Mat3 × ℤ} (hp : p ∈ delta) : GoodWord 1 p.1 := by
  simp only [delta, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨m, hm, rfl⟩
  · exact goodWord_mono goodWord_one (by norm_num)
  · exact goodWord_generator hm

theorem residualRow0_good {p : Mat3 × ℤ} (hp : p ∈ residualRow0) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  obtain ⟨a,ha,hqa⟩ := List.mem_flatMap.mp hq
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hqa
  exact goodWord_mono (goodWord_mul (delta_good ha) (delta_good hb)) (by norm_num)

theorem residualRow1_good {p : Mat3 × ℤ} (hp : p ∈ residualRow1) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mono (delta_good (p := q) hq) (by norm_num)

theorem gramPolyRow_good {a : Mat3} (ha : a ∈ basis) (r : List ℤ)
    {p : Mat3 × ℤ} (hp : p ∈ gramPolyRow a r) : GoodWord 4 p.1 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact goodWord_mul (goodWord_inv (basis_good ha)) (basis_good (List.of_mem_zip hq).1)

theorem residualRows_good {p : Mat3 × ℤ} (hp : p ∈ residualRows.flatten) : GoodWord 4 p.1 := by
  rw [residualRows_decomp] at hp
  simp only [List.flatten_cons, List.mem_append] at hp
  rcases hp with h | h | h
  · exact residualRow0_good h
  · exact residualRow1_good h
  · obtain ⟨r,hr,hp⟩ := List.mem_flatten.mp h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    exact gramPolyRow_good (List.of_mem_zip hq).1 q.2 hp

theorem residual_good {p : Mat3 × ℤ} (hp : p ∈ residual) : GoodWord 4 p.1 := by
  change p ∈ (List.range 128).flatMap residualBucket at hp
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp hp
  have h := bucket_support_original matLe residualRows allRowBuckets row_normalizations b
    (List.mem_map_of_mem (f := Prod.fst) hb)
  obtain ⟨q,hq,he⟩ := List.mem_map.mp h
  rw [← he]
  exact residualRows_good hq

end NuclearUltrapower.SOS
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem residual_value (ρ : E →* unitary A) :
    eval (value ρ) residual =
      (10000000000000 : ℤ) • (eval (value ρ) delta * eval (value ρ) delta) -
      (1000000000000 : ℤ) • eval (value ρ) delta - (10 : ℤ) • gramValue (value ρ) := by
  rw [residual_eval, residualRows_decomp]
  simp only [List.flatten_cons, eval_append]
  rw [residualRow0, eval_scale, residualRow1, eval_scale]
  have hm : eval (value ρ) (polyMul delta delta) =
      eval (value ρ) delta * eval (value ρ) delta := by
    apply eval_mul
    intro p hp q hq
    exact value_mul ρ _ _ (delta_good hp) (delta_good hq)
  rw [hm]
  have hg := eval_gram_rows (value ρ) (fun a ha b hb => by
    rw [value_mul ρ _ _ (goodWord_inv (basis_good ha)) (basis_good hb),
      value_inv ρ _ (basis_good ha)])
  rw [← List.flatMap_def, hg]
  simp only [neg_smul, sub_eq_add_neg]
  rw [add_assoc]

theorem residual_to_certificate (D Q R : A)
    (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
    (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R := by
  rw [h, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
    ← Int.cast_smul_eq_zsmul ℝ]
  norm_num only [Int.cast_ofNat]
  abel

theorem certificate_value (ρ : E →* unitary A) :
    (10000000000000 : ℝ) • (eval (value ρ) delta * eval (value ρ) delta) -
      (1000000000000 : ℝ) • eval (value ρ) delta =
      (10 : ℤ) • gramValue (value ρ) + eval (value ρ) residual := by
  exact residual_to_certificate (eval (value ρ) delta) (gramValue (value ρ))
    (eval (value ρ) residual) (residual_value ρ)

end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem operator_certificate (D Q R : H →L[ℂ] H)
    (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
    (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R := by
  rw [h]
  ext x
  simp only [add_apply, sub_apply, smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
    ← Int.cast_smul_eq_zsmul ℝ]
  norm_num only [Int.cast_ofNat]
  abel

def deltaOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta

def residualInE : List (E × ℤ) := residual.map (fun p => (eInterpret p.1, p.2))

theorem residualInE_aug : (residualInE.map Prod.snd).sum = 0 := by
  simpa only [residualInE, List.map_map, Function.comp_def, augmentation] using residual_augmentation

theorem residualInE_l1 : (residualInE.map (fun p => |p.2|)).sum = 29562852800 := by
  simpa only [residualInE, List.map_map, Function.comp_def, intL1] using residual_l1

theorem residualInE_support : ∀ p ∈ residualInE, ∃ w : List E,
    w.prod = p.1 ∧ w.length ≤ 4 ∧ ∀ s ∈ w, s ∈ eGenSet := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact eWord (residual_good hq)

theorem residualInE_operator (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    SOSEnergy.polyOperator ρ residualInE =
      eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual := by
  simp only [SOSEnergy.polyOperator, residualInE, eval, List.map_map, Function.comp_def,
    value, unitaryRep_coe]

def gramOp (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ))

theorem deltaOp_nonneg (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : 0 ≤ deltaOp ρ := delta_nonneg _

theorem gramOp_nonneg (ρ : E →* (H ≃ₗᵢ[ℂ] H)) : 0 ≤ gramOp ρ :=
  zsmul_nonneg (gramValue_nonneg _) (by norm_num)

theorem deltaOp_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 :=
  delta_energy ρ x

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

section
noncomputable section
namespace NuclearUltrapower.SOS
section
variable {A : Type*} [Ring A] [StarRing A]
theorem residual_value_generic (f : Mat3 → A)
    (hf : ∀ a ∈ delta.map Prod.fst, ∀ b ∈ delta.map Prod.fst,
      f (matMul a b) = f a * f b)
    (hg : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f residual = (10000000000000 : ℤ) • (eval f delta * eval f delta) -
      (1000000000000 : ℤ) • eval f delta - (10 : ℤ) • gramValue f := by
  rw [residual_eval, residualRows_decomp]
  simp only [List.flatten_cons, eval_append]
  rw [residualRow0, eval_scale, residualRow1, eval_scale]
  have hm : eval f (polyMul delta delta) = eval f delta * eval f delta := by
    apply eval_mul
    intro p hp q hq
    exact hf p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq)
  rw [hm]
  rw [← List.flatMap_def, eval_gram_rows f hg]
  simp only [neg_smul, sub_eq_add_neg]
  rw [add_assoc]
end
namespace ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] gramValue eval residual

theorem residual_value_native (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual =
      (10000000000000 : ℤ) • (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta *
        eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta) -
      (1000000000000 : ℤ) • eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta -
      (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)) := by
  apply residual_value_generic
  · intro a ha b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact value_mul (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (delta_good hp) (delta_good hq)
  · intro a ha b hb
    rw [value_mul (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (goodWord_inv (basis_good ha)) (basis_good hb),
      value_inv (A := H →L[ℂ] H) (unitaryRep ρ) _ (basis_good ha)]
end ElementarySpectral
end NuclearUltrapower.SOS
end
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] gramValue eval residual

theorem deltaOp_certificate (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (10000000000000 : ℝ) • (deltaOp ρ * deltaOp ρ) - (1000000000000 : ℝ) • deltaOp ρ =
      gramOp ρ + SOSEnergy.polyOperator ρ residualInE := by
  rw [residualInE_operator]
  exact operator_certificate
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta)
    (gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)))
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual)
    (residual_value_native ρ)

theorem deltaOp_sq_gap (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (1/20 : ℝ) • deltaOp ρ ≤ deltaOp ρ * deltaOp ρ :=
  SOSEnergy.certificate_sq_gap eGenSet ρ (deltaOp ρ) (gramOp ρ) residualInE
    (deltaOp_nonneg ρ) (gramOp_nonneg ρ) (deltaOp_energy ρ) residualInE_aug
    residualInE_l1 residualInE_support (deltaOp_certificate ρ)

theorem deltaOp_gap (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (deltaOp ρ).kerᗮ) :
    (1/10 : ℝ) * ‖x‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  have h := positive_sq_gap (deltaOp ρ) (deltaOp_nonneg ρ) (1/20) (deltaOp_sq_gap ρ) x hx
  rw [deltaOp_energy] at h
  linarith

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
