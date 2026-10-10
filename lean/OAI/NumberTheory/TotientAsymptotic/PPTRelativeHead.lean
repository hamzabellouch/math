import OAI.NumberTheory.TotientAsymptotic.PPTResidualSmallness
import OAI.NumberTheory.TotientAsymptotic.PPTGridSeparation
import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit

namespace OAI

/-! The head of each local dyadic suffix is large relative to that suffix's value scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- The actual inverse-cube coordinate gap makes every suffix tail a
small power of its dyadic value endpoint. The first prime therefore
satisfies the large-head hypothesis in the comparison theorem. -/
theorem ppt_local_suffix_head (d : ℕ) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ z : ℝ in atTop, ∀ (N H : ℕ) (p : Fin N → ℕ) (ω : ℝ),
      ∀ hN : 0 < N,
      (∀ i, (p i).Prime) → (∀ i, 3 ≤ p i) →
      1 ≤ H → N ≤ H → (H : ℝ) ≤ A*Real.log (B z) →
      1/(10*(H : ℝ)^3) ≤ ω → ω ≤ 1 →
      (∀ i : Fin N, 0 < i.val → B (p i) ≤ B (p ⟨0,hN⟩)/(1+ω)) →
      (p ⟨0,hN⟩-1 : ℕ) ≤ z →
      z/2 < ((d*(∏ i, p i).totient : ℕ) : ℝ) →
      z^(9/10 : ℝ) < p ⟨0,hN⟩ := by
  have hγ : 0 < 1/(80*A^3) := by positivity
  filter_upwards [B_tendsto.eventually (ppt_local_contracted_first_loss hA),
    ppt_prime_product_subpower_of_gap hA.le hγ (by norm_num : (0 : ℝ) < 1/20),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually
      (eventually_ge_atTop (2*(d : ℝ))),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    eventually_ge_atTop (Real.exp 1), eventually_gt_atTop (1 : ℝ)]
    with z hgap htail hconstant hB hzexp hz
  intro N H p ω hN hp hp3 hH hNH hdim hω hω1 hcontract hheadsize hvalue
  cases N with
  | zero => omega
  | succ k =>
    have hz0 : 0 < z := zero_lt_one.trans hz
    have ht : 0 < B z := zero_lt_one.trans hB
    have hH0 : (0 : ℝ) < H := by exact_mod_cast (zero_lt_one.trans_le hH)
    have hω0 : 0 < ω := (by positivity : 0 < 1/(10*(H : ℝ)^3)).trans_le hω
    have hden : 0 < 1+ω := by linarith only [hω0]
    have hhead : B (p 0) ≤ B z+1 := prime_coordinate_endpoint_bound (hp3 0) hzexp hheadsize
    let q : Fin k → ℕ := fun i => p i.succ
    have hcoords (i : Fin k) :
        B (q i) ≤ B z-(1/(80*A^3))*B z/(Real.log (B z))^3 := by
      have hu : B (q i)/B z ≤ (1+1/B z)/(1+ω) := by
        calc
          _ ≤ (B (p 0)/(1+ω))/B z :=
            div_le_div_of_nonneg_right (hcontract i.succ (by simp)) ht.le
          _ ≤ ((B z+1)/(1+ω))/B z :=
            div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hhead hden.le) ht.le
          _ = _ := by field_simp
      have hpad : B (q i)/B z ≤ B (q i)/B z+
          (2*(H : ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by
        have hl : 0 ≤ Real.log (B z) := (Real.log_pos hB).le
        have he : 0 ≤ (2*(H : ℝ)+3)*(2*((Real.log (B z))^5/Real.sqrt (B z))) := by positivity
        linarith only [he]
      have hh := hgap H ω (B (q i)/B z) (B (q i)/B z) hH hdim hω hω1 hu hpad
      have hh' := (div_le_iff₀ ht).mp hh
      convert hh' using 1
      ring
    have hqdim : (k : ℝ) ≤ A*Real.log (B z) :=
      (Nat.cast_le.mpr (show k ≤ H by omega)).trans hdim
    have hprod : ((∏ i, q i : ℕ) : ℝ) ≤ z^(1/20 : ℝ) :=
      htail k q (fun i => hp i.succ) hqdim hcoords
    have hφ : ((∏ i, p i).totient : ℝ) ≤ (p 0 : ℝ)*((∏ i, q i : ℕ) : ℝ) := by
      calc
        _ ≤ ((∏ i, p i : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.totient_le (∏ i, p i))
        _ = _ := by rw [Fin.prod_univ_succ, Nat.cast_mul]
    have hp0 : 0 ≤ (p 0 : ℝ) := Nat.cast_nonneg _
    have hstep : z < (2*(d : ℝ))*(p 0 : ℝ)*z^(1/20 : ℝ) := by
      have hprod' := mul_le_mul_of_nonneg_left hprod hp0
      have hφ' := hφ.trans hprod'
      have hh := mul_le_mul_of_nonneg_left hφ' (Nat.cast_nonneg d)
      push_cast at hvalue
      nlinarith only [hh, hvalue]
    have hstep' : z < (p 0 : ℝ)*z^(1/10 : ℝ) := by
      apply hstep.trans_le
      calc
        _ ≤ z^(1/20 : ℝ)*(p 0 : ℝ)*z^(1/20 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant hp0)
            (Real.rpow_pos_of_pos hz0 _).le
        _ = (p 0 : ℝ)*z^((1/20 : ℝ)+1/20) := by rw [Real.rpow_add hz0]; ring
        _ = _ := by norm_num
    have hzpow : z = z^(9/10 : ℝ)*z^(1/10 : ℝ) := by
      rw [← Real.rpow_add hz0]
      norm_num
    nth_rw 1 [hzpow] at hstep'
    exact (mul_lt_mul_iff_left₀ (Real.rpow_pos_of_pos hz0 (1/10 : ℝ))).mp hstep'


/-- Direct specialization to any suffix of the constructed geometric
prime family. Its actual first coordinate controls the local dimension
and supplies the required contraction. -/
theorem ppt_geometric_suffix_head (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, ∀ (m n : ℕ) (budget : ℝ) (p : Fin n → ℕ),
      n ≤ m → (∀ j, (p j).Prime) → (∀ j, 3 ≤ p j) →
      primePrefixCoord p ∈ relaxedGeometricFamily m n budget c →
      ∀ i : Fin n, (p i-1 : ℕ) ≤ z →
        z/2 < ((d*(∏ j, primeFinal p i.val j).totient : ℕ) : ℝ) →
        z^(9/10 : ℝ) < p i := by
  filter_upwards [ppt_local_suffix_head d (ppt_local_dimension_constant_pos c),
    ppt_local_prime_dimension hc] with z hhead hdim
  intro m n budget p hnm hp hp3 hgeom i hsize hvalue
  have hH : 1 ≤ m-i.val := by have := i.isLt; omega
  have hN : 0 < n-i.val := Nat.sub_pos_of_lt i.isLt
  have hNle : n-i.val ≤ m-i.val := Nat.sub_le_sub_right hnm _
  have hdim' := hdim (m-i.val) (p i) (hp3 i) (hgeom.2.1 i) hsize
  have hzero : primeFinal p i.val ⟨0,hN⟩ = p i := by
    apply congrArg p
    apply Fin.ext
    simp only [Nat.add_zero]
  let ω : ℝ := 1/(10*((m-i.val : ℕ) : ℝ)^3)
  have hHr : (1 : ℝ) ≤ (m-i.val : ℕ) := by exact_mod_cast hH
  have hω1 : ω ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 10*((m-i.val : ℕ) : ℝ)^3)).mpr
    have hh : (1 : ℝ) ≤ ((m-i.val : ℕ) : ℝ)^3 := one_le_pow₀ hHr
    linarith only [hh]
  have herr : rowContractionError (m-(i.val+1))/2 = ω := by
    have he : m-(i.val+1)+1 = m-i.val := by have := i.isLt; omega
    have her : ((m-(i.val+1) : ℕ) : ℝ)+1 = ((m-i.val : ℕ) : ℝ) := by exact_mod_cast he
    dsimp only [rowContractionError, ω]
    rw [her]
    ring
  have hcontract (j : Fin (n-i.val)) (hj : 0 < j.val) :
      B (primeFinal p i.val j) ≤ B (primeFinal p i.val ⟨0,hN⟩)/(1+ω) := by
    let k : Fin n := ⟨i.val+j.val,by have := j.isLt; omega⟩
    have hik : i < k := by change i.val < i.val+j.val; omega
    have hh := hgeom.2.2 i k hik
    change B (p k) ≤ B (p i)/(1+rowContractionError (m-(i.val+1))/2) at hh
    rw [herr] at hh
    have hpk : primeFinal p i.val j = p k := by
      apply congrArg p
      apply Fin.ext
      simp only [k]
    rw [hpk,hzero]
    exact hh
  have hh := hhead (n-i.val) (m-i.val) (primeFinal p i.val) ω hN
    (fun j => hp _) (fun j => hp3 _) hH hNle hdim' le_rfl hω1 hcontract
    (by simpa only [hzero] using hsize) hvalue
  simpa only [hzero] using hh

end TotientAsymptotic

end

end OAI
