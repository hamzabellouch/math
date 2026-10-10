import OAI.Geometry.Convex.GeneralMahler.Spectral
import OAI.Geometry.Convex.GeneralMahler.Bias

namespace OAI
/-! Spectral boxes and clipping; normalization preparation. -/
noncomputable section
open Set Filter Real Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ}

def specBox (m : ℕ) (a b : ℝ) : Set (Mat m) :=
  {A | A.IsHermitian ∧ scalar m a ≤ A ∧ A ≤ scalar m b}

lemma op_scalar (a : ℝ) (v:Rn m) : op (scalar m a) v = a • v := by
  simp only [scalar,_root_.map_smul,_root_.map_one,_root_.smul_apply]
  rfl

lemma form_scalar (a : ℝ) (v:Rn m) : ⟪v,op (scalar m a) v⟫ = a * ‖v‖^2 := by
  rw [op_scalar,real_inner_smul_right,real_inner_self_eq_norm_sq]

lemma scalar_le' (a b : ℝ) (hab:a ≤ b) : scalar m a ≤ scalar m b := by
  refine (op_order_iff (scalar_sym ..) (scalar_sym ..)).mpr fun v=>?_
  rw [form_scalar,form_scalar]; gcongr

lemma mem_box_form {A : Mat m} {a b:ℝ} :
    A∈specBox m a b ↔ A.IsHermitian ∧
      (∀ v, a * ‖v‖^2 ≤ ⟪v,op A v⟫) ∧ ∀ v, ⟪v,op A v⟫ ≤ b * ‖v‖^2 := by
  change (_ ∧ _) ↔ _
  apply and_congr_right; intro h
  rw [op_order_iff (scalar_sym ..) h, op_order_iff h (scalar_sym ..)]
  simp only [form_scalar]

lemma specBox_compact (a b:ℝ) : IsCompact (specBox m a b) := by
  let K := |a|+|b|
  have h₁ : ∀ A∈specBox m a b, ‖A‖ ≤ K := by
    intro A h
    apply spectrum_norm_box (by dsimp [K]; positivity) h.1
    · apply le_trans _ h.2.1; apply scalar_le'
      unfold K; linarith [neg_abs_le a,abs_nonneg b]
    apply le_trans h.2.2
    apply scalar_le'; unfold K; linarith [le_abs_self b,abs_nonneg a]
  have hc : IsClosed (specBox m a b) := by
    have h : specBox m a b =
        {A:Mat m|star A=A} ∩ ((⋂ v:Rn m,{A|a*‖v‖^2≤ opPair v v A}) ∩
          (⋂ v:Rn m,{A|opPair v v A ≤ b*‖v‖^2})) := by
      ext; simp only [mem_inter_iff, mem_iInter,mem_ofPred_eq,opPair_apply,mem_box_form]; rfl
    rw [h]
    exact (isClosed_eq continuous_star continuous_id).inter ((isClosed_iInter fun i =>
      isClosed_le continuous_const (opPair i i).continuous).inter (isClosed_iInter fun i =>
        isClosed_le (opPair i i).continuous continuous_const))
  exact (isCompact_closedBall (0:Mat m) K).of_isClosed_subset hc (by intro x hx; simpa using h₁ x hx)

lemma specBox_convex (a b:ℝ) : Convex ℝ (specBox m a b) := by
  intro x hx y hy l k hl hk hlk
  rw [mem_box_form] at hx hy ⊢
  have he (v : Rn m) :
      ⟪v,op (l • x+k • y) v⟫ = l * ⟪v,op x v⟫ + k*⟪v,op y v⟫ := by
    change opPair v v _ = l * opPair v v _ + k*opPair v v _
    simp only [_root_.map_add,_root_.map_smul,smul_eq_mul]
  refine ⟨(hx.1.smul (show IsSelfAdjoint l from rfl)).add
    (hy.1.smul (show IsSelfAdjoint k from rfl)),fun v => ?_,fun v => ?_⟩
  · rw [he]
    have hi := add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 v) hl)
      (mul_le_mul_of_nonneg_left (hy.2.1 v) hk)
    rwa [← add_mul,hlk,one_mul] at hi
  rw [he]
  have hi := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2 v) hl)
    (mul_le_mul_of_nonneg_left (hy.2.2 v) hk)
  rwa [← add_mul,hlk,one_mul] at hi

lemma specBox_nonempty (m : ℕ) (a b:ℝ) (h:a ≤ b) : (specBox m a b).Nonempty :=
  ⟨scalar m a,scalar_sym ..,le_rfl,scalar_le' _ _ h⟩

def clip (a b:ℝ) (A : Mat m) := cfc (fun x : ℝ => max a (min x b)) A

lemma cont_clip (a b:ℝ) : ContinuousOn (clip a b) {A : Mat m|A.IsHermitian} :=
  cfc_continuous_herm _ (by fun_prop)

lemma clip_mem (a b:ℝ) (hab:a ≤ b) {A : Mat m} (hA:A.IsHermitian) :
    clip a b A ∈ specBox m a b := by
  obtain ⟨h,h'⟩ := scalar_cfc_order (fun x:ℝ=>max a (min x b)) A hA (l := a) (r := b)
  exact ⟨cfc_herm .., h.mpr (fun _ _ => le_max_left ..),
    h'.mpr (fun _ _ => max_le hab (min_le_right ..))⟩

/-- If the projection update B ↦ clip(B+M) is fixed
and neither kind of extreme eigenvector with wrong outward sign exists,
then no clipping occurs and M=0. -/
lemma clip_eq {a b:ℝ} (hab:a ≤ b) {B M:Mat m}
    (he : clip a b (B+M)=B) (h : (B+M).IsHermitian)
    (h₁ : ∀ v : Rn m, ‖v‖=1 → op B v=a • v → 0 ≤ ⟪v,op M v⟫)
    (h₂ : ∀ v : Rn m, ‖v‖=1 → op B v=b • v → ⟪v,op M v⟫ ≤ 0) : M=0 := by
  let f := fun x:ℝ=>max a (min x b)
  have hb : ∀ i, f (h.eigenvalues i)=h.eigenvalues i := by
    intro i
    let v := h.eigenvectorBasis i
    let x := h.eigenvalues i
    change f x=x
    have hh : op B v=f x • v := by
      have hi := cfc_eigen' f h i
      change op (clip a b (B+M)) v=_ at hi
      rwa [he] at hi
    have hv : ‖v‖=1 := h.eigenvectorBasis.orthonormal.1 _
    have hw : ⟪v,op M v⟫ = x-f x := by
      have h : op (B+M) v=x • v := op_eigen h i
      rw [_root_.map_add,_root_.add_apply,hh] at h
      have he := congrArg (fun y=>inner ℝ v y) h
      rw [inner_add_right,real_inner_smul_right,real_inner_smul_right, real_inner_self_eq_norm_sq,hv] at he
      linarith
    rcases lt_or_ge x a with hx|hx
    · have he : f x=a := max_eq_left ((min_le_left ..).trans hx.le)
      have H := h₁ _ hv (he ▸ hh); rw [hw, he] at H; linarith
    rcases le_or_gt x b with hy|hy
    · dsimp [f]; rw [min_eq_left hy,max_eq_right hx]
    have he : f x=b := by dsimp [f]; rw [min_eq_right hy.le,max_eq_right hab]
    have H := h₂ _ hv (he ▸ hh); rw [hw,he] at H; linarith
  have hn : IsSelfAdjoint (B+M) := h
  have hu : clip a b (B+M)= B+M := by
    conv_rhs => rw [← cfc_id ℝ (B+M)]
    apply cfc_congr
    rw [h.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i,rfl⟩; apply hb
  rw [he] at hu; simpa [eq_comm] using hu

lemma form_posDef {a b : ℝ} (ha:0<a) {A:Mat m} (hm : A∈specBox m a b) :
    A.PosDef := by
  rw [op_posDef_iff]
  rw [mem_box_form] at hm
  exact ⟨hm.1,fun x hx => (mul_pos ha (pow_pos (norm_pos_iff.mpr hx) _)).trans_le (hm.2.1 x)⟩

end GeneralMahler

end

end OAI
