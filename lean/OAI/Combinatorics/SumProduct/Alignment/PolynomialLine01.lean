import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction14
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance polynomialLine01BinomialTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem degree_general_leibman_binomial
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ b : Fin (t+d)→ℤ, b≠0 ∧ (∀ i, |(b i:ℝ)|≤A) ∧ (∀ a b : G, ξ (a*b*a⁻¹*b⁻¹)=1) ∧
          (∀ g : G, (ξ g).toAdd=∑ i, c.coord g i*(b i:ℝ)) ∧
        ∃ α : ℕ→ℝ, (∀ j : ℕ, s<j → α j=0) ∧
          (∀ z : ℤ, (ξ (f z)).toAdd=∑ j : Fin (s+1), α j.val*(Ring.choose z j.val:ℤ)) ∧
          ∀ j : ℕ, 0<j → (N:ℝ)^j*‖(α j : UnitAddCircle)‖≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,C,hC,hprod⟩ := degree_general_metric_producer c hsk H h0 h1 s hs
    q hqbound hq Γ hΓ htop μ δ hδ
  let S : ℝ := ∑ ξ∈U, ∑ i, |(ξ (axis c i 1)).toAdd|
  have hS : 0≤S := Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  let A : ℝ := 1+S+BinomialDifference.conversionBound s*C
  have hconv : 0<BinomialDifference.conversionBound s*C :=
    mul_pos (BinomialDifference.conversionBound_pos s) hC
  have hA : 0<A := by dsimp [A]; linarith
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf hdisc
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
  obtain ⟨b,hb⟩ := integer_character_coordinates c hsk ξ Γ hΓ hξc hξΓ
  have hbi (i : Fin (t+d)) : (b i:ℝ)=(ξ (axis c i 1)).toAdd := by
    rw [hb]
    simp [coord_axis,Pi.single_apply]
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,b,?_,?_,?_,hb,
    fun j => BinomialDifference.coefficient ℝ j P,?_,?_,?_⟩
  · intro hb0
    apply hξ0
    ext g
    apply Multiplicative.toAdd.injective
    change (ξ g).toAdd=0
    rw [hb,hb0]
    simp
  · intro i
    have h1 : |(ξ (axis c i 1)).toAdd| ≤ ∑ j, |(ξ (axis c j 1)).toAdd| :=
      Finset.single_le_sum (f := fun j : Fin (t+d) => |(ξ (axis c j 1)).toAdd|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ j, |(ξ (axis c j 1)).toAdd|)≤S :=
      Finset.single_le_sum (f := fun χ : G→*Multiplicative ℝ => ∑ j, |(χ (axis c j 1)).toAdd|) (fun χ _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hξ
    rw [hbi]
    dsimp [A]
    linarith
  · intro a b
    apply Multiplicative.toAdd.injective
    simp only [map_mul,map_inv,toAdd_mul,toAdd_inv]
    change (ξ a).toAdd+(ξ b).toAdd+(-(ξ a).toAdd)+(-(ξ b).toAdd)=0
    ring
  · intro j hj
    exact BinomialDifference.coefficient_eq_zero ℝ j P (hP.trans_lt hj)
  · exact character_binomial_expansion H s hs hf ξ P hPe
  · intro j hj
    have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
    have hbnd := BinomialDifference.coefficient_bound s 1 P hP (N:ℝ) C hNr hC.le
      (fun i hi => hPc i hi) j hj
    apply hbnd.trans
    dsimp [A]
    linarith

end SquareInduction
end
end
 

 
section
 
namespace IntegerGridInterpolation
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section

abbrev Grid (n d : ℕ) := Fin n → Fin (d + 1)

def weight (d : ℕ) (j t : Fin (d + 1)) : ℚ :=
  (Lagrange.basis Finset.univ (fun t : Fin (d + 1) => (t.val : ℚ)) t).coeff j.val

theorem one_dimensional (d : ℕ) (j k : Fin (d + 1)) :
    ∑ t : Fin (d + 1), weight d j t * (t.val : ℚ) ^ k.val =
      if j = k then 1 else 0 := by
  classical
  have hinj : Set.InjOn (fun t : Fin (d + 1) => (t.val : ℚ))
      (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) := by
    intro a _ b _ hab
    apply Fin.ext
    exact_mod_cast (show (a.val : ℚ) = b.val from hab)
  have hp : (X ^ k.val : ℚ[X]).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    simp only [degree_X_pow, Finset.card_univ, Fintype.card_fin, Nat.cast_lt]
    exact_mod_cast k.isLt
  have h := congrArg (fun p : ℚ[X] => p.coeff j.val)
    (Lagrange.eq_interpolate (v := fun t : Fin (d + 1) => (t.val : ℚ))
      hinj hp : (X ^ k.val : ℚ[X]) = _)
  simp only [Lagrange.interpolate_apply, finsetSum_coeff, eval_pow, eval_X,
    coeff_C_mul, coeff_X_pow] at h
  simpa only [weight, mul_comm, Fin.ext_iff] using h.symm

def tensorWeight (n d : ℕ) (e v : Grid n d) : ℚ := ∏ i, weight d (e i) (v i)

theorem tensor_orthogonality (n d : ℕ) (e f : Grid n d) :
    ∑ v : Grid n d, tensorWeight n d e v * (∏ i, ((v i).val : ℚ) ^ (f i).val) =
      if e = f then 1 else 0 := by
  classical
  simp only [tensorWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (t : Fin (d + 1)) => weight d (e i) t * (t.val : ℚ) ^ (f i).val)]
  simp_rw [one_dimensional]
  by_cases h : e = f
  · subst f; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem reconstruction (n d : ℕ) (a : Grid n d → ℚ) (e : Grid n d) :
    ∑ v : Grid n d, tensorWeight n d e v *
      (∑ f : Grid n d, a f * ∏ i, ((v i).val : ℚ) ^ (f i).val) = a e := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (tensorWeight n d e _) (a _)]
  simp_rw [← Finset.mul_sum]
  change (∑ f : Grid n d, a f * (∑ v : Grid n d, tensorWeight n d e v * ∏ i, ((v i).val : ℚ) ^ (f i).val)) = a e
  simp_rw [tensor_orthogonality]
  simp

theorem clear_denominators {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ (B : ℕ), 0 < B ∧ ∃ w : ι → ℤ, ∀ i, (B : ℚ) * f i = w i := by
  classical
  let B := ∏ i, (f i).den
  have hB : 0 < B := Finset.prod_pos (fun i _ => (f i).den_pos)
  refine ⟨B, hB, (fun i => (B / (f i).den : ℕ) * (f i).num), ?_⟩
  intro i
  have hd : (f i).den ∣ B := Finset.dvd_prod_of_mem (fun i => (f i).den) (Finset.mem_univ i)
  have he : (B : ℚ) = ((B / (f i).den : ℕ) : ℚ) * (f i).den := by
    exact_mod_cast (Nat.div_mul_cancel hd).symm
  have hq : ((f i).den : ℚ) * f i = (f i).num := by
    rw [mul_comm]
    exact (eq_div_iff (by exact_mod_cast (f i).den_ne_zero)).mp (f i).num_div_den.symm
  rw [he, mul_assoc, hq]
  push_cast
  rfl

theorem exists_integer_weights (n d : ℕ) :
    ∃ B : ℕ, 0 < B ∧ ∃ w : Grid n d → Grid n d → ℤ,
      ∀ e f : Grid n d,
        ∑ v : Grid n d, (w e v : ℝ) * ∏ i, ((v i).val : ℝ) ^ (f i).val =
          if e = f then (B : ℝ) else 0 := by
  classical
  obtain ⟨B, hB, w, hw⟩ := clear_denominators
    (fun p : Grid n d × Grid n d => tensorWeight n d p.1 p.2)
  refine ⟨B, hB, (fun e v => w (e, v)), ?_⟩
  intro e f
  have hh : ∀ v, (w (e,v) : ℝ) = (B : ℝ) * (tensorWeight n d e v : ℝ) := by
    intro v
    exact_mod_cast (hw (e,v)).symm
  simp_rw [hh, mul_assoc]
  rw [← Finset.mul_sum]
  have hid : (∑ v : Grid n d, (tensorWeight n d e v : ℝ) *
      ∏ i, ((v i).val : ℝ) ^ (f i).val) = if e = f then 1 else 0 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (tensor_orthogonality n d e f)
    push_cast at h
    split_ifs at h ⊢ <;> simpa only [Rat.cast_one, Rat.cast_zero] using h
  rw [hid]
  split_ifs <;> simp

theorem real_reconstruction {n d B : ℕ} (w : Grid n d → Grid n d → ℤ)
    (hw : ∀ e f : Grid n d,
      ∑ v : Grid n d, (w e v : ℝ) * ∏ i, ((v i).val : ℝ) ^ (f i).val =
        if e = f then (B : ℝ) else 0)
    (a : Grid n d → ℝ) (e : Grid n d) :
    ∑ v : Grid n d, (w e v : ℝ) *
      (∑ f : Grid n d, a f * ∏ i, ((v i).val : ℝ) ^ (f i).val) = B * a e := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (w e _ : ℝ) (a _)]
  simp_rw [← Finset.mul_sum, hw]
  simp [mul_comm]

end
end IntegerGridInterpolation

 
namespace PolynomialLineCoefficients
open scoped BigOperators
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section

abbrev Grid (n d : ℕ) := Fin n → Fin (d + 1)
def totalDegree {n d : ℕ} (e : Grid n d) : ℕ := ∑ i, (e i).val

def natLine {n d : ℕ} (e : Grid n d) (x v : Fin n → ℕ) : ℕ[X] :=
  ∏ i, (C (x i) + C (v i) * X) ^ (e i).val

theorem linear_degree (x v : ℕ) : (C x + C v * X : ℕ[X]).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le

theorem prod_degree {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ[X]) (d : ι → ℕ) (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
  (natDegree_prod_le s f).trans (Finset.sum_le_sum hd)

theorem prod_top_coeff {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ[X]) (d : ι → ℕ) (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    rw [coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))
      (prod_degree s f d (fun j hj => hd j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]

theorem natLine_degree {n d : ℕ} (e : Grid n d) (x v : Fin n → ℕ) :
    (natLine e x v).natDegree ≤ totalDegree e := by
  apply prod_degree
  intro i _
  simpa using natDegree_pow_le_of_le (e i).val (linear_degree (x i) (v i))

theorem natLine_coeff_zero {n d j : ℕ} (e : Grid n d) (x v : Fin n → ℕ)
    (hj : totalDegree e < j) : (natLine e x v).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natLine_degree e x v).trans_lt hj)

theorem natLine_top_coeff {n d : ℕ} (e : Grid n d) (x v : Fin n → ℕ) :
    (natLine e x v).coeff (totalDegree e) = ∏ i, v i ^ (e i).val := by
  rw [natLine, totalDegree, prod_top_coeff]
  · apply Finset.prod_congr rfl
    intro i _
    have hh := coeff_pow_of_natDegree_le (m := (e i).val) (linear_degree (x i) (v i))
    simpa using hh
  · intro i _
    simpa using natDegree_pow_le_of_le (e i).val (linear_degree (x i) (v i))

theorem coeff_times_pow_le_eval (p : ℕ[X]) (j N : ℕ) :
    p.coeff j * N ^ j ≤ p.eval N := by
  classical
  rw [eval_eq_sum, Polynomial.sum]
  by_cases hj : j ∈ p.support
  · exact Finset.single_le_sum (f := fun i => p.coeff i * N ^ i) (fun i _ => Nat.zero_le _) hj
  · have hh : p.coeff j = 0 := notMem_support_iff.mp hj
    simp [hh]

theorem totalDegree_le {n d : ℕ} (e : Grid n d) : totalDegree e ≤ n * d := by
  calc
    _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (e i).isLt)
    _ = _ := by simp

theorem natLine_eval_bound {n d N : ℕ} (e : Grid n d) (x v : Fin n → ℕ)
    (hx : ∀ i, x i ≤ N) (hv : ∀ i, v i ≤ d) :
    (natLine e x v).eval N ≤ ((d + 1) * N) ^ totalDegree e := by
  simp only [natLine, eval_prod, eval_pow, eval_add, eval_C, eval_mul, eval_X]
  rw [totalDegree, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _)
  intro i _
  apply Nat.pow_le_pow_left
  nlinarith [hx i, hv i]

theorem natLine_coeff_bound {n d N j : ℕ} (hN : 0 < N) (e : Grid n d)
    (x v : Fin n → ℕ) (hx : ∀ i, x i ≤ N) (hv : ∀ i, v i ≤ d)
    (hj : j ≤ totalDegree e) :
    ((natLine e x v).coeff j : ℝ) ≤ (d + 1 : ℝ) ^ (n * d) * (N : ℝ) ^ (totalDegree e - j) := by
  have h := (coeff_times_pow_le_eval (natLine e x v) j N).trans (natLine_eval_bound e x v hx hv)
  have h' : ((natLine e x v).coeff j : ℝ) * (N : ℝ) ^ j ≤
      ((d + 1 : ℝ) * N) ^ totalDegree e := by exact_mod_cast h
  have hp : 0 < (N : ℝ) ^ j := pow_pos (Nat.cast_pos.mpr hN) _
  apply (mul_le_mul_iff_left₀ hp).mp
  have he : (N : ℝ) ^ (totalDegree e - j) * N ^ j = N ^ totalDegree e := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  calc
    _ ≤ ((d + 1 : ℝ) * N) ^ totalDegree e := h'
    _ ≤ (d + 1 : ℝ) ^ (n * d) * (N : ℝ) ^ totalDegree e := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith : (1 : ℝ) ≤ d + 1) (totalDegree_le e))
        (pow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [mul_assoc, he]

def line {n d : ℕ} (a : Grid n d → ℝ) (x v : Fin n → ℕ) : ℝ[X] :=
  ∑ e : Grid n d, C (a e) * (natLine e x v).map (Nat.castRingHom ℝ)

theorem line_coeff {n d : ℕ} (a : Grid n d → ℝ) (x v : Fin n → ℕ) (j : ℕ) :
    (line a x v).coeff j = ∑ e : Grid n d, a e * ((natLine e x v).coeff j : ℝ) := by
  simp [line, finsetSum_coeff]

theorem line_eval {n d : ℕ} (a : Grid n d → ℝ) (x v : Fin n → ℕ) (t : ℕ) :
    (line a x v).eval (t : ℝ) =
      ∑ e : Grid n d, a e * ∏ i, ((x i + t * v i : ℕ) : ℝ) ^ (e i).val := by
  simp only [line, eval_finsetSum, eval_mul, eval_C, eval_map, eval₂_at_natCast,
    natLine, eval_prod, eval_pow, eval_add, eval_C, eval_mul, eval_X]
  push_cast
  simp only [mul_comm (v _ : ℝ) (t : ℝ)]

theorem line_degree {n d : ℕ} (a : Grid n d → ℝ) (x v : Fin n → ℕ) :
    (line a x v).natDegree ≤ n * d := by
  apply natDegree_sum_le_of_forall_le
  intro e _
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_map_le.trans ((natLine_degree e x v).trans (totalDegree_le e)))

end
end PolynomialLineCoefficients

 

end
end
end
end

end OAI
