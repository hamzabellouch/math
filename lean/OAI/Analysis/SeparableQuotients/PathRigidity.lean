import OAI.Analysis.SeparableQuotients.PathStabilization

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

/-- Legal crop selecting an interval of original weights, without recoding. -/
def FinitePath.weightCrop {f : Family} (P : FinitePath f) (J T : ℕ) : Crop where
  ordinal := {a | (∀ i : Fin P.length, P.raw.weight i < J → ∀ b ∈ (P.raw.piece i).support, b < a) ∧
    (∀ i : Fin P.length, T < P.raw.weight i → ∀ b ∈ (P.raw.piece i).support, a < b)}
  ordinal_convex := ⟨by
    intro a ha b hb z hz
    exact ⟨fun i hi x hx => (ha.1 i hi x hx).trans_le hz.1,
      fun i hi x hx => hz.2.trans_lt (hb.2 i hi x hx)⟩⟩
  colors := Set.univ
  colors_convex := Set.ordConnected_univ

lemma FinitePath.weightCrop_set {f : Family} (P : FinitePath f) (J T : ℕ) :
    (P.weightCrop J T).set f = (P.weightCrop J T).ordinal := by
  cases f <;> simp only [Crop.set, weightCrop, Set.preimage_univ, Set.inter_univ]

lemma FinitePath.weightCrop_piece {f : Family} (P : FinitePath f) (J T : ℕ) (i : Fin P.length) :
    restrict ((P.weightCrop J T).set f) (P.raw.piece i) =
      if J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T then P.raw.piece i else 0 := by
  rw [P.weightCrop_set]
  ext a
  rw [restrict_apply]
  by_cases hi : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T
  · rw [ite_eq_left hi]
    by_cases hia : P.raw.piece i a = 0
    · simp only [hia, ite_self]
    · have ha : a ∈ (P.weightCrop J T).ordinal := by
        refine ⟨fun j hj b hb => ?_, fun j hj b hb => ?_⟩
        · have hji : j < i := P.valid.weight_strict.lt_iff_lt.mp (hj.trans_le hi.1)
          exact P.valid.successive j i hji i.isLt b hb a (Finsupp.mem_support_iff.mpr hia)
        · have hij : i < j := P.valid.weight_strict.lt_iff_lt.mp (hi.2.trans_lt hj)
          exact P.valid.successive i j hij j.isLt a (Finsupp.mem_support_iff.mpr hia) b hb
      rw [ite_eq_left ha]
  · rw [ite_eq_right hi]
    by_cases hia : P.raw.piece i a = 0
    · simp only [hia, ite_self, Finsupp.zero_apply]
    · have ha : a ∉ (P.weightCrop J T).ordinal := by
        intro ha
        rcases lt_or_ge (P.raw.weight i) J with h | h
        · exact (lt_irrefl a) (ha.1 i h a (Finsupp.mem_support_iff.mpr hia))
        · have ht : T < P.raw.weight i := lt_of_not_ge (fun hh => hi ⟨h, hh⟩)
          exact (lt_irrefl a) (ha.2 i ht a (Finsupp.mem_support_iff.mpr hia))
      simp only [ite_eq_right ha, Finsupp.zero_apply]

def FinitePath.window {f : Family} (P : FinitePath f) (J T : ℕ) : Array :=
  ∑ i : Fin P.length, if J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T then P.raw.piece i else 0

def FinitePath.windowWeights {f : Family} (P : FinitePath f) (J T : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin P.length => J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T)).image
    (fun i : Fin P.length => P.raw.weight i)

lemma FinitePath.weightCrop_value {f : Family} (P : FinitePath f) (J T : ℕ) :
    restrict ((P.weightCrop J T).set f) P.value = P.window J T := by
  simp only [FinitePath.value, restrict_sum, P.weightCrop_piece, window]

lemma FinitePath.weightCrop_active {f : Family} (P : FinitePath f) (J T : ℕ) :
    P.active (P.weightCrop J T) = P.windowWeights J T := by
  unfold active windowWeights
  apply congrArg (Finset.image (fun i : Fin P.length => P.raw.weight i))
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, P.weightCrop_piece]
  split_ifs with hi
  · exact iff_of_true (P.raw.nonzero i) hi
  · exact iff_of_false (by simp) hi

lemma FinitePath.mem_windowWeights {f : Family} (P : FinitePath f) (J T w : ℕ) :
    w ∈ P.windowWeights J T ↔ J ≤ w ∧ w ≤ T ∧ ∃ i : Fin P.length, P.raw.weight i = w := by
  simp only [windowWeights, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi.1, hi.2, i, rfl⟩
  · rintro ⟨hJ, hT, i, rfl⟩
    exact ⟨i, ⟨hJ, hT⟩, rfl⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
@[reducible] local instance dualEGroup13 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace13 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

def croppedPathFunctional {f : Family} (P : FinitePath f) (A : Crop) : StrongDual ℝ E :=
  (norming.rationalPredual (restrict (A.set f) P.value)).val

lemma rational_cropped_path_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℚ) (hc : ∑ i, |(c i : ℝ)| ^ f.q ≤ 1) :
    ‖∑ i, (c i : ℝ) • croppedPathFunctional (P i) (A i)‖ ≤ 1 := by
  let e : TypeII f := ⟨h, P, A, c, hc, hdis⟩
  have he : e.value ∈ Full := f.norming_subset_full (e.mem_family hm)
  have heq : norming.functional ⟨e.value, he⟩ =
      ∑ i, (c i : ℝ) • croppedPathFunctional (P i) (A i) := by
    ext x
    rw [← norming.evaluateArray_eq_functional]
    simp only [e, TypeII.value, map_sum, map_rat_smul, Rat.smul_def,
      sum_apply, smul_apply, smul_eq_mul, croppedPathFunctional, NormingSet.evaluateArray]
    rfl
  rw [← heq]
  exact norming.norm_functional_le _

lemma real_cropped_path_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j))))
    (c : Fin h → ℝ) :
    ‖∑ i, c i • croppedPathFunctional (P i) (A i)‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  apply RealCoefficients.bound_from_unit f.q hq
  exact RealCoefficients.rational_to_real f.q hq _ (rational_cropped_path_bound P A hm hdis)

lemma cropped_abs_sum_bound {f : Family} {h : ℕ} (P : Fin h → FinitePath f)
    (A : Fin h → Crop) (hm : ∀ b i j, ((P b).piece i).child j ∈ f.norming)
    (hdis : Pairwise (fun i j => Disjoint ((P i).active (A i)) ((P j).active (A j)))) (x : E) :
    (∑ i, |croppedPathFunctional (P i) (A i) x|) ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := by
  let c : Fin h → ℝ := fun i => RealCoefficients.signChoice (croppedPathFunctional (P i) (A i) x)
  have hc (i : Fin h) : |c i| = 1 := RealCoefficients.abs_signChoice _
  have hv (i : Fin h) : c i * croppedPathFunctional (P i) (A i) x =
      |croppedPathFunctional (P i) (A i) x| := RealCoefficients.signChoice_mul _
  have he : (∑ i, c i • croppedPathFunctional (P i) (A i)) x =
      ∑ i, |croppedPathFunctional (P i) (A i) x| := by
    simp only [sum_apply, smul_apply, smul_eq_mul, hv]
  calc
    _ = |(∑ i, c i • croppedPathFunctional (P i) (A i)) x| := by
      rw [he, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    _ ≤ ‖∑ i, c i • croppedPathFunctional (P i) (A i)‖ * ‖x‖ :=
      by simpa only [Real.norm_eq_abs] using (∑ i, c i • croppedPathFunctional (P i) (A i)).le_opNorm x
    _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [hc, Real.one_rpow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      using (real_cropped_path_bound P A hm hdis c)) (norm_nonneg _)

lemma window_disjoint_cap {f : Family} (M δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ (h : ℕ) (P : Fin h → FinitePath f) (J T : ℕ) (x : E),
      (∀ b i j, ((P b).piece i).child j ∈ f.norming) →
      Pairwise (fun i j => Disjoint ((P i).windowWeights J T) ((P j).windowWeights J T)) →
      ‖x‖ ≤ M → (∀ b, δ < |norming.evaluateArray x ((P b).window J T)|) → h ≤ K := by
  have hq : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
  obtain ⟨K, hK⟩ := PathSelection.power_cap (1/f.q) M δ
    ((div_lt_one (by linarith)).mpr (by linarith)) hδ
  refine ⟨K, fun h P J T x hm hdis hx hh => hK h ?_⟩
  have he (b : Fin h) : croppedPathFunctional (P b) ((P b).weightCrop J T) x =
      norming.evaluateArray x ((P b).window J T) := by
    simp only [croppedPathFunctional, (P b).weightCrop_value, NormingSet.evaluateArray]
    rfl
  calc
    δ * (h : ℝ) = ∑ _b : Fin h, δ := by simp [mul_comm]
    _ ≤ ∑ b, |croppedPathFunctional (P b) ((P b).weightCrop J T) x| :=
      Finset.sum_le_sum (fun b _ => by rw [he b]; exact (hh b).le)
    _ ≤ (h : ℝ) ^ (1/f.q) * ‖x‖ := cropped_abs_sum_bound P _ hm
      (by simpa only [FinitePath.weightCrop_active] using hdis) x
    _ ≤ M * (h : ℝ) ^ (1/f.q) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

/-- Actual pieces, original weights, and original metadata below a threshold.
This is deliberately not the compressed history, nor a cropped code. -/
def FinitePath.lowHistory {f : Family} (P : FinitePath f) (J : ℕ) : Set (Array × ℕ × ℕ) :=
  {d | d.2.1 < J ∧ ∃ i : Fin P.length,
    d = (P.raw.piece i, P.raw.weight i, P.raw.metadata i)}

lemma PrefixValid.metadata_mono {P : RawPath} {len : ℕ} (hP : PrefixValid P len)
    {i j : ℕ} (hij : i ≤ j) (hj : j < len) : P.metadata i ≤ P.metadata j := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (hP.metadata_strict i j h hj).le

lemma FinitePath.code_of_shared_weight {f : Family} (P Q : FinitePath f)
    (i : Fin P.length) (j : Fin Q.length) (hi : 0 < i.val) (hj : 0 < j.val)
    (hw : P.raw.weight i = Q.raw.weight j) :
    i.val = j.val ∧ P.raw.code (i.val-1) = Q.raw.code (i.val-1) := by
  have hc : P.raw.code (i.val-1) = Q.raw.code (j.val-1) := by
    apply sigma_injective
    rw [← P.valid.rule (i.val-1) (by omega), ← Q.valid.rule (j.val-1) (by omega)]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i.val),
      Nat.sub_add_cancel (by omega : 1 ≤ j.val)] using hw
  have heq := RawPath.code_eq_length hc
  have hij : i.val = j.val := by omega
  exact ⟨hij, by simpa only [hij] using hc⟩

lemma closure_downward_rho (β a b : Γ) (p : ℕ) (hp : 1 ≤ p)
    (hab : a ≤ b) (hb : b ∈ F β p) (hr : rho a b ≤ p) : a ∈ F β p := by
  have ha := (rho_le_iff a b hab p hp).mp hr
  rw [F_coherent β b p hb] at ha
  exact (Finset.mem_filter.mp ha).1

/-- Two agreeing compressed histories whose later pieces meet one finite
coordinate set with sufficiently small rho have identical actual earlier
pieces. The anchors may be different coordinates and different pieces. -/
lemma PrefixValid.low_piece_eq_of_anchors {P Q : RawPath} {len len' n i j k : ℕ}
    (hP : PrefixValid P len) (hQ : PrefixValid Q len')
    (hn : n < len) (hn' : n < len') (hc : P.code n = Q.code n)
    (hij : i < j) (hik : i < k) (hjn : j ≤ n) (hkn : k ≤ n)
    (a b : Γ) (ha : a ∈ (P.piece j).support) (hb : b ∈ (Q.piece k).support)
    (hr : rho (min a b) (max a b) ≤ P.metadata n) : P.piece i = Q.piece i := by
  have hm := (RawPath.code_eq_at hc n le_rfl).2.1
  rcases le_total a b with hab | hba
  · have haQ : a ∈ Q.closure n := by
      have hbQ := hQ.piece_support_subset_closure hkn hn' hb
      unfold RawPath.closure at hbQ ⊢
      apply closure_downward_rho _ a b _ (hQ.metadata_pos n hn') hab hbQ
      simpa only [min_eq_left hab, max_eq_right hab, hm] using hr
    exact hP.piece_eq_of_code_anchor hQ hn hn' hij hjn hc a ha haQ
  · have hbP : b ∈ P.closure n := by
      have haP := hP.piece_support_subset_closure hjn hn ha
      unfold RawPath.closure at haP ⊢
      apply closure_downward_rho _ b a _ (hP.metadata_pos n hn) hba haP
      simpa only [min_eq_right hba, max_eq_left hba] using hr
    exact (hQ.piece_eq_of_code_anchor hP hn' hn hik hkn hc.symm b hb hbP).symm

lemma FinitePath.lowHistory_eq_of_code_anchors {f : Family} (P Q : FinitePath f)
    (J n : ℕ) (hn : n < P.length) (hn' : n < Q.length) (hc : P.raw.code n = Q.raw.code n)
    (j : Fin P.length) (k : Fin Q.length) (hjn : j.val ≤ n) (hkn : k.val ≤ n)
    (hj : J ≤ P.raw.weight j) (hk : J ≤ Q.raw.weight k)
    (a b : Γ) (ha : a ∈ (P.raw.piece j).support) (hb : b ∈ (Q.raw.piece k).support)
    (hr : rho (min a b) (max a b) ≤ P.raw.metadata n) : P.lowHistory J = Q.lowHistory J := by
  have hleft (i : Fin P.length) (hi : P.raw.weight i < J) :
      ∃ i' : Fin Q.length, P.raw.piece i = Q.raw.piece i' ∧
        P.raw.weight i = Q.raw.weight i' ∧ P.raw.metadata i = Q.raw.metadata i' := by
    have hij : i < j := P.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hj)
    have hin : i.val ≤ n := (show i.val ≤ j.val from hij.le).trans hjn
    let i' : Fin Q.length := ⟨i.val, hin.trans_lt hn'⟩
    have he := RawPath.code_eq_at hc i hin
    have hik : i' < k := Q.valid.weight_strict.lt_iff_lt.mp
      (by change Q.raw.weight i < Q.raw.weight k; rw [← he.1]; exact hi.trans_le hk)
    exact ⟨i', P.valid.low_piece_eq_of_anchors Q.valid hn hn' hc hij hik hjn hkn a b ha hb hr,
      he.1, he.2.1⟩
  have hright (i : Fin Q.length) (hi : Q.raw.weight i < J) :
      ∃ i' : Fin P.length, Q.raw.piece i = P.raw.piece i' ∧
        Q.raw.weight i = P.raw.weight i' ∧ Q.raw.metadata i = P.raw.metadata i' := by
    have hik : i < k := Q.valid.weight_strict.lt_iff_lt.mp (hi.trans_le hk)
    have hin : i.val ≤ n := (show i.val ≤ k.val from hik.le).trans hkn
    let i' : Fin P.length := ⟨i.val, hin.trans_lt hn⟩
    have he := RawPath.code_eq_at hc i hin
    have hij : i' < j := P.valid.weight_strict.lt_iff_lt.mp
      (by change P.raw.weight i < P.raw.weight j; rw [he.1]; exact hi.trans_le hj)
    exact ⟨i', (P.valid.low_piece_eq_of_anchors Q.valid hn hn' hc hij hik hjn hkn a b ha hb hr).symm,
      he.1.symm, he.2.1.symm⟩
  ext d
  constructor
  · rintro ⟨hd, i, rfl⟩
    obtain ⟨i', hp, hw, hm⟩ := hleft i hd
    exact ⟨hd, i', by rw [hp, hw, hm]⟩
  · rintro ⟨hd, i, rfl⟩
    obtain ⟨i', hp, hw, hm⟩ := hright i hd
    exact ⟨hd, i', by rw [hp, hw, hm]⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

lemma FinitePath.lowHistory_eq_of_shared_later_weight {f : Family} (P Q : FinitePath f)
    (Jv Tv Jt Tt Jk Tk : ℕ) (hvt : Tv < Jt) (htk : Tt < Jk)
    (j : Fin P.length) (k : Fin Q.length) (t : Fin P.length)
    (hj : Jv ≤ P.raw.weight j ∧ P.raw.weight j ≤ Tv)
    (hk : Jv ≤ Q.raw.weight k ∧ Q.raw.weight k ≤ Tv)
    (ht : Jt ≤ P.raw.weight t ∧ P.raw.weight t ≤ Tt)
    (a b : Γ) (ha : a ∈ (P.raw.piece j).support) (hb : b ∈ (Q.raw.piece k).support)
    (hr : rho (min a b) (max a b) ≤ Jt)
    (hw : ∃ w, w ∈ P.windowWeights Jk Tk ∧ w ∈ Q.windowWeights Jk Tk) :
    P.lowHistory Jv = Q.lowHistory Jv := by
  obtain ⟨w, hwP, hwQ⟩ := hw
  obtain ⟨hwJ, _, i, hei⟩ := (P.mem_windowWeights Jk Tk w).mp hwP
  obtain ⟨_, _, i', hei'⟩ := (Q.mem_windowWeights Jk Tk w).mp hwQ
  have htw : P.raw.weight t < P.raw.weight i := by omega
  have hti : t < i := P.valid.weight_strict.lt_iff_lt.mp htw
  have htJ : Jt ≤ Tt := ht.1.trans ht.2
  have hji : j < i := P.valid.weight_strict.lt_iff_lt.mp (by omega)
  have hki' : k < i' := Q.valid.weight_strict.lt_iff_lt.mp (by omega)
  have hi : 0 < i.val := (Nat.zero_le t.val).trans_lt hti
  have hi' : 0 < i'.val := (Nat.zero_le k.val).trans_lt hki'
  obtain ⟨he, hc⟩ := P.code_of_shared_weight Q i i' hi hi' (hei.trans hei'.symm)
  have hn : i.val - 1 < P.length := by omega
  have hn' : i.val - 1 < Q.length := by have := i'.isLt; omega
  have htn : t.val ≤ i.val - 1 := by omega
  have hmn : Jt ≤ P.raw.metadata (i.val-1) := ht.1.trans
    ((P.valid.weight_le_metadata t t.isLt).trans (P.valid.metadata_mono htn hn))
  exact P.lowHistory_eq_of_code_anchors Q Jv (i.val-1) hn hn' hc j k
    (by omega) (by omega) hj.1 hk.1 a b ha hb (hr.trans hmn)

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def FinitePath.lowHistoryFinset {f : Family} (P : FinitePath f) (J : ℕ) : Finset (Array × ℕ × ℕ) :=
  (Finset.univ.filter (fun i : Fin P.length => P.raw.weight i < J)).image
    (fun i : Fin P.length => (P.raw.piece i, P.raw.weight i, P.raw.metadata i))

lemma FinitePath.mem_lowHistoryFinset {f : Family} (P : FinitePath f) (J : ℕ)
    (d : Array × ℕ × ℕ) : d ∈ P.lowHistoryFinset J ↔ d ∈ P.lowHistory J := by
  simp only [lowHistoryFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    lowHistory, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i, rfl⟩
  · rintro ⟨hd, i, rfl⟩
    exact ⟨i, hd, rfl⟩

lemma FinitePath.window_eq_sum_lowHistory {f : Family} (P : FinitePath f) (J T H : ℕ)
    (hT : T < H) : P.window J T =
      ∑ d ∈ P.lowHistoryFinset H, if J ≤ d.2.1 ∧ d.2.1 ≤ T then d.1 else 0 := by
  rw [lowHistoryFinset, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T
    · simp only [hi, and_self, ite_true, ite_eq_left (hi.2.trans_lt hT)]
    · simp only [hi, ite_false, ite_self]
  · intro i _ j _ he
    apply P.valid.weight_strict.injective
    exact congrArg (fun d : Array × ℕ × ℕ => d.2.1) he

lemma FinitePath.window_eq_of_lowHistory {f : Family} (P Q : FinitePath f) (J T H : ℕ)
    (hT : T < H) (he : P.lowHistory H = Q.lowHistory H) : P.window J T = Q.window J T := by
  have hf : P.lowHistoryFinset H = Q.lowHistoryFinset H := by
    ext d
    rw [P.mem_lowHistoryFinset, Q.mem_lowHistoryFinset, he]
  rw [P.window_eq_sum_lowHistory J T H hT, Q.window_eq_sum_lowHistory J T H hT, hf]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- A finite path with its original finite-stage children. -/
def LegalFinitePath (f : Family) := {P : FinitePath f // ∀ i j, (P.piece i).child j ∈ f.norming}

def WindowHit {f : Family} (P : LegalFinitePath f) (x : Γ →₀ ℝ) (J T : ℕ) (δ : ℝ) : Prop :=
  δ < |norming.evaluateArray (norming.includeFinite x) (P.val.window J T)|

lemma window_anchor {f : Family} (P : FinitePath f) (x : Γ →₀ ℝ) (J T : ℕ)
    (hh : norming.evaluateArray (norming.includeFinite x) (P.window J T) ≠ 0) :
    ∃ i : Fin P.length, J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T ∧
      ∃ a ∈ x.support, a ∈ (P.raw.piece i).support := by
  simp only [FinitePath.window, map_sum] at hh
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
  have hw : J ≤ P.raw.weight i ∧ P.raw.weight i ≤ T := by
    by_contra hn
    simp only [ite_eq_right hn, map_zero, ne_eq, not_true_eq_false] at hi
  rw [ite_eq_left hw, norming.evaluateArray_eq] at hi
  obtain ⟨a, ha, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨i, hw.1, hw.2, a, ?_, ha⟩
  rw [norming.coordinate_includeFinite] at hh
  exact Finsupp.mem_support_iff.mpr (fun hz => hh (by rw [hz, mul_zero]))

lemma WindowHit.anchor {f : Family} {P : LegalFinitePath f} {x : Γ →₀ ℝ}
    {J T : ℕ} {δ : ℝ} (hδ : 0 < δ) (hh : WindowHit P x J T δ) :
    ∃ i : Fin P.val.length, J ≤ P.val.raw.weight i ∧ P.val.raw.weight i ≤ T ∧
      ∃ a ∈ x.support, a ∈ (P.val.raw.piece i).support := by
  apply window_anchor
  exact abs_pos.mp (hδ.trans hh)

/-- Rigidity of two path histories with shared later weights. -/
lemma disjoint_of_different_histories {f : Family} (P Q : LegalFinitePath f)
    (x : Γ →₀ ℝ) (Jv Tv Jt Tt Jk Tk : ℕ) (hvt : Tv < Jt) (htk : Tt < Jk)
    (δ : ℝ) (hδ : 0 < δ)
    (hp : WindowHit P x Jv Tv δ) (hq : WindowHit Q x Jv Tv δ)
    (ht : ∃ t : Fin P.val.length, Jt ≤ P.val.raw.weight t ∧ P.val.raw.weight t ≤ Tt)
    (hr : ∀ a ∈ x.support, ∀ b ∈ x.support, rho (min a b) (max a b) ≤ Jt)
    (hne : P.val.lowHistory Jv ≠ Q.val.lowHistory Jv) :
    Disjoint (P.val.windowWeights Jk Tk) (Q.val.windowWeights Jk Tk) := by
  obtain ⟨j, hj, hj', a, ha, ha'⟩ := hp.anchor hδ
  obtain ⟨k, hk, hk', b, hb, hb'⟩ := hq.anchor hδ
  obtain ⟨t, ht, ht'⟩ := ht
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  exact hne (P.val.lowHistory_eq_of_shared_later_weight Q.val Jv Tv Jt Tt Jk Tk hvt htk
    j k t ⟨hj, hj'⟩ ⟨hk, hk'⟩ ⟨ht, ht'⟩ a b ha' hb' (hr a ha b hb) ⟨w, hw, hw'⟩)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

/-- Uniform finite covers from the history-class argument. -/
lemma finite_window_covers {f : Family} (x : ℕ → Γ →₀ ℝ) (J T : ℕ → ℕ)
    (horder : ∀ i j, i < j → T i < J j)
    (hcoh : ∀ i j, i < j → ∀ a ∈ (x i).support, ∀ b ∈ (x i).support,
      rho (min a b) (max a b) ≤ J j)
    (M δ : ℝ) (hM : ∀ i, ‖norming.includeFinite (x i)‖ ≤ M) (hδ : 0 < δ)
    (hall : ∀ w v t k : ℕ, w < v → v < t → t < k →
      ∃ P : LegalFinitePath f, WindowHit P (x w) (J w) (T w) δ ∧
        WindowHit P (x v) (J v) (T v) δ ∧ WindowHit P (x t) (J t) (T t) δ ∧
        WindowHit P (x k) (J k) (T k) δ) :
    ∃ D : ℕ, ∀ n, ∃ R : Finset (LegalFinitePath f), R.card ≤ D ∧
      ∀ i ≤ n, ∃ P ∈ R, WindowHit P (x i) (J i) (T i) δ := by
  obtain ⟨D, hD⟩ := window_disjoint_cap (f := f) M δ hδ
  refine ⟨D, fun n => ?_⟩
  have hex (i : Fin (n+1)) := hall i (n+1) (n+2) (n+3) i.isLt (by omega) (by omega)
  choose P hP using hex
  let H : Fin (n+1) → Set (Array × ℕ × ℕ) := fun i => (P i).val.lowHistory (J (n+1))
  let S : Finset (Set (Array × ℕ × ℕ)) := Finset.univ.image H
  have hrep (d : S) : ∃ i : Fin (n+1), H i = d.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp d.property
    exact ⟨i, hi⟩
  let rep : S → Fin (n+1) := fun d => (hrep d).choose
  have hr (d : S) : H (rep d) = d.val := (hrep d).choose_spec
  let e : Fin S.card ≃ S := S.equivFin.symm
  let Q : Fin S.card → LegalFinitePath f := fun b => P (rep (e b))
  have hQ (b : Fin S.card) : (Q b).val.lowHistory (J (n+1)) = (e b).val := hr (e b)
  have hcard : S.card ≤ D := by
    apply hD S.card (fun b => (Q b).val) (J (n+3)) (T (n+3)) (norming.includeFinite (x (n+3)))
      (fun b => (Q b).property)
    · intro b c hbc
      apply disjoint_of_different_histories (Q b) (Q c) (x (n+1)) (J (n+1)) (T (n+1))
        (J (n+2)) (T (n+2)) (J (n+3)) (T (n+3)) (horder _ _ (by omega))
        (horder _ _ (by omega)) δ hδ
      · exact (hP _).2.1
      · exact (hP _).2.1
      · obtain ⟨i, hi, hi', a, ha, ha'⟩ := ((hP (rep (e b))).2.2.1).anchor hδ
        exact ⟨i, hi, hi'⟩
      · exact hcoh _ _ (by omega)
      · rw [hQ, hQ]
        exact fun hh => hbc (e.injective (Subtype.ext hh))
    · exact hM (n+3)
    · intro b
      exact (hP (rep (e b))).2.2.2
  refine ⟨Finset.univ.image Q, (Finset.card_image_le).trans (by simpa using hcard), fun i hi => ?_⟩
  let ii : Fin (n+1) := ⟨i, by omega⟩
  let d : S := ⟨H ii, Finset.mem_image.mpr ⟨ii, Finset.mem_univ _, rfl⟩⟩
  let b := e.symm d
  have hh : (Q b).val.lowHistory (J (n+1)) = (P ii).val.lowHistory (J (n+1)) := by
    rw [hQ]
    exact congrArg Subtype.val (e.apply_symm_apply d)
  refine ⟨Q b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩, ?_⟩
  change δ < |norming.evaluateArray _ ((Q b).val.window (J i) (T i))|
  rw [(Q b).val.window_eq_of_lowHistory (P ii).val (J i) (T i) (J (n+1))
    (horder i (n+1) (by omega)) hh]
  exact (hP ii).1

end SeparableQuotient.ActualSpace

end

end OAI
