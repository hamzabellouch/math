import OAI.Analysis.PlanarPacking.Cardinal

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def hexPoint (v : ℤ×ℤ) : Plane :=
  WithLp.toLp 2 ![((v.1:ℝ)+(v.2:ℝ)/2)/Real.sqrt b, Real.sqrt b*(v.2:ℝ)]
def hexForm (v : ℤ×ℤ) : ℤ := v.1^2+v.1*v.2+v.2^2
def hexNat (v : ℤ×ℤ) : ℕ := (hexForm v).toNat
lemma hexForm_nonneg (v : ℤ×ℤ) : 0 ≤ hexForm v := by
  unfold hexForm
  nlinarith [sq_nonneg (2*v.1+v.2),sq_nonneg v.2]
lemma hexForm_zero_iff (v : ℤ×ℤ) : hexForm v=0 ↔ v=0 := by
  constructor
  · intro hv
    have h1 : v.1=0 := by
      have h := sq_nonneg (v.1+2*v.2)
      unfold hexForm at hv
      nlinarith [sq_nonneg v.1,sq_nonneg v.2]
    have h2 : v.2=0 := by simpa [hexForm,h1] using hv
    exact Prod.ext h1 h2
  · rintro rfl; norm_num [hexForm]
lemma hexNat_coe (v : ℤ×ℤ) : (hexNat v:ℤ)=hexForm v := Int.toNat_of_nonneg (hexForm_nonneg v)
lemma hexNat_zero_iff (v : ℤ×ℤ) : hexNat v=0 ↔ v=0 := by
  rw [← hexForm_zero_iff]
  have hh := hexNat_coe v
  omega
lemma hexNat_pos {v : ℤ×ℤ} (hv : v≠0) : 0<hexNat v := Nat.pos_of_ne_zero ((hexNat_zero_iff v).not.mpr hv)
lemma hexResidue_table : ∀ a c : Fin 12,
    (a.val^2+a.val*c.val+c.val^2)%12 ∈ residues := by decide +kernel
lemma hexNat_residue (v : ℤ×ℤ) : hexNat v%12∈residues := by
  have ha : 0 ≤ v.1%12 := Int.emod_nonneg _ (by norm_num)
  have hc : 0 ≤ v.2%12 := Int.emod_nonneg _ (by norm_num)
  have ha' : (v.1%12).toNat<12 := by omega
  have hc' : (v.2%12).toNat<12 := by omega
  have hh := hexResidue_table ⟨(v.1%12).toNat,ha'⟩ ⟨(v.2%12).toNat,hc'⟩
  have he : (hexNat v:ℤ)%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2:ℕ)%12 := by
    rw [hexNat_coe]
    push_cast
    rw [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hc]
    simp only [hexForm,pow_two,Int.add_emod,Int.mul_emod,Int.emod_emod]
  have he' : hexNat v%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2)%12 := by exact_mod_cast he
  rw [he']; exact hh
noncomputable def hexNode (v : ℤ×ℤ) (hv : v≠0) : Node := ⟨hexNat v,hexNat_pos hv,hexNat_residue v⟩
lemma hexPoint_radius (v : ℤ×ℤ) : b*‖hexPoint v‖^2=(hexNat v:ℝ) := by
  have hb : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr b_pos).ne'
  have hs := Real.sq_sqrt b_pos.le
  have hn : (hexNat v:ℝ)=(v.1:ℝ)^2+(v.1:ℝ)*(v.2:ℝ)+(v.2:ℝ)^2 := by
    exact_mod_cast hexNat_coe v
  rw [hn,EuclideanSpace.norm_sq_eq]
  simp only [hexPoint,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
  rw [div_pow,mul_pow,hs]
  field_simp [b_pos.ne']
  nlinarith [b_sq]
def firstShell : Finset (ℤ×ℤ) := {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)}
lemma firstShell_card : firstShell.card=6 := by decide +kernel
lemma firstShell_iff (v : ℤ×ℤ) : hexNat v=1 ↔ v∈firstShell := by
  have he : hexNat v=1 ↔ hexForm v=1 := by
    constructor <;> intro hh
    · simpa [hh] using (hexNat_coe v).symm
    · rw [hexNat,hh]; rfl
  rw [he]
  constructor
  · intro hv
    have h1 : -1 ≤ v.1 ∧ v.1 ≤ 1 := by
      have hh:=sq_nonneg (v.1+2*v.2)
      unfold hexForm at hv
      constructor <;> nlinarith [sq_nonneg v.1,sq_nonneg v.2]
    have h2 : -1 ≤ v.2 ∧ v.2 ≤ 1 := by
      have hh:=sq_nonneg (2*v.1+v.2)
      unfold hexForm at hv
      constructor <;> nlinarith [sq_nonneg v.1,sq_nonneg v.2]
    rcases v with ⟨j,k⟩
    rcases h1 with ⟨h11,h12⟩
    rcases h2 with ⟨h21,h22⟩
    interval_cases j <;> interval_cases k <;> norm_num [firstShell,hexForm] at *
  · intro hv
    simp only [firstShell,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with h|h|h|h|h|h <;> rw [h] <;> norm_num [hexForm]
end SharpPlanar

end OAI
