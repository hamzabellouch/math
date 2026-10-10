import OAI.Analysis.StrictMeans.SmoothGridRegular

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def latticeCoord : Lattice →+ ℂ where
  toFun v := ((ofLex v).1:ℂ)+((ofLex v).2:ℂ)*Complex.I
  map_zero' := by simp
  map_add' v w := by simp [add_mul]; ring

@[simp] lemma latticeCoord_ex : latticeCoord ex = 1 := by simp [latticeCoord,ex]
@[simp] lemma latticeCoord_ey : latticeCoord ey = Complex.I := by simp [latticeCoord,ey]
@[simp] lemma latticeCoord_re (v : Lattice) : (latticeCoord v).re = (ofLex v).1 := by simp [latticeCoord]
@[simp] lemma latticeCoord_im (v : Lattice) : (latticeCoord v).im = (ofLex v).2 := by simp [latticeCoord]

def meshPoint (o : ℂ) (s : ℝ) (v : Lattice) : ℂ := o+s•latticeCoord v

lemma meshPoint_add (o : ℂ) (s : ℝ) (v w : Lattice) :
    meshPoint o s (v+w) = meshPoint o s v+s•latticeCoord w := by
  simp [meshPoint,smul_add,add_assoc]
lemma meshPoint_sub (o : ℂ) (s : ℝ) (v w : Lattice) :
    meshPoint o s (v-w) = meshPoint o s v-s•latticeCoord w := by
  simp [meshPoint,smul_sub,add_sub_assoc]

lemma StarCertificate.toRegularStar {u : ℂ → ℝ} {o : ℂ} {s : ℝ} {v : Lattice}
    (h : StarCertificate u (meshPoint o s v) 1 Complex.I s) :
    RegularStar (u ∘ meshPoint o s) ex ey v := by
  simpa only [StarCertificate,RegularStar,Function.comp_apply,meshPoint_add,
    meshPoint_sub,map_add,latticeCoord_ex,latticeCoord_ey,smul_add,add_assoc] using h

lemma latticeCoord_injective : Injective latticeCoord := by
  intro v w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [latticeCoord_re,latticeCoord_im] at hr hi
  exact ofLex.injective (Prod.ext (by exact_mod_cast hr) (by exact_mod_cast hi))

lemma meshPoint_injective {o : ℂ} {s : ℝ} (hs : s ≠ 0) : Injective (meshPoint o s) := by
  intro v w h
  exact latticeCoord_injective ((smul_right_injective ℂ hs) (add_left_cancel h))

lemma meshPoint_bounded_preimage {o : ℂ} {s : ℝ} (hs : s≠0) {K : Set ℂ}
    (hK : Bornology.IsBounded K) : (meshPoint o s ⁻¹' K).Finite := by
  obtain ⟨R,hR⟩ := hK.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((R+‖o‖)/|s|)
  apply ((Set.finite_Icc (- (N:ℤ)) N).prod (Set.finite_Icc (-(N:ℤ)) N)).preimage
    ofLex.injective.injOn |>.subset
  intro v hv
  have hb : ‖s•latticeCoord v‖≤R+‖o‖ := by
    have h := norm_sub_le (meshPoint o s v) o
    have he : meshPoint o s v-o=s•latticeCoord v := by simp [meshPoint]
    rw [he] at h
    exact h.trans (add_le_add (hR _ hv) le_rfl)
  have hc : ‖latticeCoord v‖ < (N:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs] at hb
    exact (le_div_iff₀ (abs_pos.mpr hs)).mpr (by simpa [mul_comm] using hb) |>.trans_lt hN
  have hx : |((ofLex v).1:ℝ)| < (N:ℝ) := by simpa only [latticeCoord_re] using (Complex.abs_re_le_norm _).trans_lt hc
  have hy : |((ofLex v).2:ℝ)| < (N:ℝ) := by simpa only [latticeCoord_im] using (Complex.abs_im_le_norm _).trans_lt hc
  constructor <;> constructor
  · exact_mod_cast (abs_lt.mp hx).1.le
  · exact_mod_cast (abs_lt.mp hx).2.le
  · exact_mod_cast (abs_lt.mp hy).1.le
  · exact_mod_cast (abs_lt.mp hy).2.le

lemma norm_latticeCoord_star {v w : Lattice} (hw : w ∈ meshStar ex ey v) :
    ‖latticeCoord w-latticeCoord v‖≤2 := by
  simp only [meshStar,Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simp
  · simp
  · simpa only [map_add,latticeCoord_ex,latticeCoord_ey,add_sub_cancel_left,
      show ∀ a : ℂ, a+1+Complex.I-a=1+Complex.I by intro a; ring] using
      (norm_add_le (1:ℂ) Complex.I).trans (by norm_num)
  · simp
  · simp
  · have he : latticeCoord (v-(ex+ey))-latticeCoord v=-(1+Complex.I) := by simp
    rw [he,norm_neg]
    exact (norm_add_le (1:ℂ) Complex.I).trans (by norm_num)
  · simp

lemma meshPoint_star_dist {o : ℂ} {s : ℝ} {v w : Lattice}
    (hw : w ∈ meshStar ex ey v) : dist (meshPoint o s w) (meshPoint o s v) ≤ 2*|s| := by
  rw [dist_eq_norm]
  have he : meshPoint o s w-meshPoint o s v=s•(latticeCoord w-latticeCoord v) := by
    simp [meshPoint,smul_sub]
  rw [he,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_latticeCoord_star hw) (abs_nonneg s)).trans_eq (mul_comm _ _)

lemma meshBoundary_annulus {o p : ℂ} {s r : ℝ} {S : Finset Lattice}
    (hS : ∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) {v : Lattice}
    (hv : v ∈ meshBoundary ex ey S) :
    r-2*|s| < dist (meshPoint o s v) p ∧ dist (meshPoint o s v) p ≤r+2*|s| := by
  obtain ⟨⟨w,hw,hwS⟩,hb⟩ := (mem_meshBoundary _ _ _ _).mp hv
  obtain ⟨a,ha,haS⟩ := Finset.not_subset.mp hb
  have hwi := (hS w).mp hwS
  have hao : r < dist (meshPoint o s a) p := lt_of_not_ge (fun he => haS ((hS a).mpr he))
  have h₁ := dist_triangle (meshPoint o s a) (meshPoint o s v) p
  have h₂ := dist_triangle (meshPoint o s v) (meshPoint o s w) p
  have ha' := meshPoint_star_dist (o:=o) (s:=s) ha
  have hw' := meshPoint_star_dist (o:=o) (s:=s) hw
  rw [dist_comm (meshPoint o s w) (meshPoint o s v)] at hw'
  constructor <;> linarith

end
end StrictInverseFirstPower.Grid

end

end OAI
