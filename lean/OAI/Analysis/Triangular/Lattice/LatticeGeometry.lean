import OAI.Analysis.Triangular.Energy.Mixtures
import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AtomicTriangular
lemma triangular_scale_eq : (Real.sqrt b)⁻¹=Real.sqrt (2/Real.sqrt 3) := by
  rw [←Real.sqrt_inv]
  congr 1
  simp [b,inv_div]
lemma triangularPoint_eq_support (v : ℤ × ℤ) : triangularPoint v=TriangularUniversal.triangularPoint v := by
  unfold triangularPoint TriangularUniversal.triangularPoint
  rw [triangular_scale_eq]
  congr 2
  unfold b
  ring_nf
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2=3/4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
lemma triangularPoint_norm_sq (j k : ℤ) :
    b*‖triangularPoint (j,k)‖^2=(j:ℝ)^2+(j:ℝ)*k+(k:ℝ)^2 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_norm_sq j k
lemma A_eq_support : A=TriangularUniversal.triangularLattice := by
  unfold A TriangularUniversal.triangularLattice
  congr 1
  exact funext triangularPoint_eq_support
lemma eisenstein_mod36_finite : ∀ j k : Fin 36,
    ((j.val:ℤ)^2+(j.val:ℤ)*k.val+(k.val:ℤ)^2)%36∈Construction.residues := by decide +kernel
lemma eisenstein_mod36 (j k : ℤ) :
    (j^2+j*k+k^2)%36∈Construction.residues := by
  let j' : Fin 36 := ⟨(j%36).toNat,by have := Int.emod_nonneg j (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos j (by norm_num : (0:ℤ)<36); omega⟩
  let k' : Fin 36 := ⟨(k%36).toNat,by have := Int.emod_nonneg k (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<36); omega⟩
  have hj : (j'.val:ℤ)=j%36 := Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
  have hk : (k'.val:ℤ)=k%36 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hh := eisenstein_mod36_finite j' k'
  rw [hj,hk] at hh
  simpa [Int.add_emod,Int.mul_emod,pow_two,Int.emod_emod] using hh
lemma A_radial_node {x : Plane} (hx : x∈A) (hx0 : x≠0) :
    ∃ n : Construction.Node,Construction.radial x=n.val := by
  obtain ⟨⟨j,k⟩,rfl⟩ := hx
  let n : ℤ := j^2+j*k+k^2
  have he : Construction.radial (triangularPoint (j,k))=(n:ℝ) := by
    change b*‖triangularPoint (j,k)‖^2=_
    rw [triangularPoint_norm_sq]
    dsimp [n]
    push_cast
    rfl
  have hn : 0 < n := by
    have hp : 0 < Construction.radial (triangularPoint (j,k)) :=
      mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hx0))
    rw [he] at hp
    exact_mod_cast hp
  exact ⟨⟨n,hn,eisenstein_mod36 j k⟩,he⟩
lemma dualA_integer_coordinates {w : Plane} (hw : w∈dualA) :
    ∃ j k : ℤ,w 0=(Real.sqrt b)*(j:ℝ) ∧ (Real.sqrt b)*w 1=(k:ℝ)-(j:ℝ)/2 := by
  obtain ⟨j,hj⟩ := hw (triangularPoint (1,0)) ⟨(1,0),rfl⟩
  obtain ⟨k,hk⟩ := hw (triangularPoint (0,1)) ⟨(0,1),rfl⟩
  have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
  have hp : 0 < Real.sqrt b := Real.sqrt_pos.mpr b_pos
  simp [triangularPoint,inner_smul_left,inner_add_left,EuclideanSpace.inner_single_left] at hj hk
  refine ⟨j,k,?_,?_⟩
  · field_simp at hj
    nlinarith
  · field_simp at hj hk
    apply (mul_left_cancel₀ hp.ne')
    nlinarith [congrArg (fun t : ℝ => t*w 1) hr]
lemma dualA_radial_node {w : Plane} (hw : w∈dualA) (hw0 : w≠0) :
    ∃ n : Construction.Node,Construction.radial w=n.val := by
  obtain ⟨j,k,hj,hk⟩ := dualA_integer_coordinates hw
  let n : ℤ := j^2-j*k+k^2
  have he : Construction.radial w=(n:ℝ) := by
    change b*‖w‖^2=_
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
    simp only [Real.norm_eq_abs,sq_abs]
    have hr : (Real.sqrt b)^2=b := Real.sq_sqrt b_pos.le
    have hb := b_sq
    have hk' := congrArg (fun t : ℝ => t^2) hk
    rw [mul_pow,hr] at hk'
    rw [hj,mul_pow,hr]
    dsimp [n]
    push_cast
    nlinarith
  have hn : 0 < n := by
    have hpos : 0 < Construction.radial w := mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hw0))
    rw [he] at hpos
    exact_mod_cast hpos
  have hm : n%36∈Construction.residues := by
    convert eisenstein_mod36 j (-k) using 1
    dsimp [n]
    congr 1
    ring
  exact ⟨⟨n,hn,hm⟩,he⟩
end AtomicTriangular
end

end OAI
