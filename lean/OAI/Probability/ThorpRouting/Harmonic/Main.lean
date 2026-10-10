import Mathlib
import OAI.Probability.ThorpRouting.Harmonic.Site

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.Casimir
open scoped BigOperators Classical

theorem palindrome_cost_mgf_coarse (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ 1/32) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  have hd : d ≤ 1*4^d := by have hh := pow_four_ge d; omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω = palindromeLowCost 1 d e ω+
      (palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω) := by
    have hh := palindromeCost_family 1 d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    simpa only [Nat.add_assoc] using hh.symm
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hlow (ω : BenesCoins d) : q^(palindromeLowCost 1 d e ω) ≤ Real.exp (Fintype.card ι) := by
    calc
      _ ≤ q^(Fintype.card ι) := pow_le_pow_right₀ hq (by simpa using palindromeLowCost_le 1 d e ω)
      _ = Real.exp (Fintype.card ι*Real.log q) := by rw [Real.exp_nat_mul,Real.exp_log hqp]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  calc
    _ ≤ finiteMean (fun ω : BenesCoins d => Real.exp (Fintype.card ι)*
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [hcost,pow_add]
      exact mul_le_mul_of_nonneg_right (hlow ω) (pow_nonneg hqp.le _)
    _ = Real.exp (Fintype.card ι)*finiteMean (fun ω : BenesCoins d =>
        q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) := by simpa only [mul_comm] using finiteMean_mul_const (fun ω : BenesCoins d => q^(palindromeFamilyCost 1 d d e ω+palindromeFamilyCost 2 d d e ω)) (Real.exp (Fintype.card ι))
    _ ≤ Real.exp (Fintype.card ι)*Real.exp (Fintype.card ι*heightDecay 1) := by
      exact mul_le_mul_of_nonneg_left
        (palindrome_high_full_mgf 1 d d (by decide) e q hq hlog) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma row_moment_coarse (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d)
    (a : ℝ) (ha : 0 < a) (ha32 : a ≤ 1/32) :
    palindromeRowMoment d e a ≤ Real.exp (Fintype.card ι*(1+heightDecay 1)) := by
  let q : ℝ := (2:ℝ)^a
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) ha.le
  have hlog : Real.log q ≤ 1/32 := by
    dsimp [q]
    rw [Real.log_rpow (by norm_num)]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    nlinarith
  have hn : (0:ℝ) < ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ) ≤ ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ) /
      ((2^d:ℕ):ℝ)^(Fintype.card ι) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hpow := Real.rpow_le_one hn0 hn1 ha.le
  have hm := palindrome_row_density_moment d e a ha.le
  have he (c : ℕ) : q^c = (2:ℝ)^((c:ℝ)*a) := by
    rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  simp_rw [←he] at hm
  exact (hm.trans (mul_le_of_le_one_left (finiteMean_nonneg (fun _ =>
    pow_nonneg (le_trans (by norm_num) hq) _)) hpow)).trans
      (palindrome_cost_mgf_coarse d e q hq hlog)


lemma applyKernel_mul {X : Type*} [Fintype X] (P Q : Matrix X X ℝ)
    (v : EuclideanSpace ℂ X) :
    DensityTransfer.applyKernel (fun x y => (P*Q) x y) v =
      DensityTransfer.applyKernel (fun x y => P x y) (DensityTransfer.applyKernel (fun x y => Q x y) v) := by
  apply PiLp.ext
  intro x
  change DensityTransfer.applyKernel (fun x y => (P*Q) x y) v x = DensityTransfer.applyKernel (fun x y => P x y) (DensityTransfer.applyKernel (fun x y => Q x y) v) x
  simp only [DensityTransfer.applyKernel_apply,Matrix.mul_apply,Complex.ofReal_sum,
    Complex.ofReal_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma applyKernel_one {X : Type*} [Fintype X] [DecidableEq X]
    (v : EuclideanSpace ℂ X) : DensityTransfer.applyKernel (fun x y => (1 : Matrix X X ℝ) x y) v = v := by
  apply PiLp.ext
  intro x
  change DensityTransfer.applyKernel (fun x y => (1 : Matrix X X ℝ) x y) v x = v x
  simp [DensityTransfer.applyKernel_apply,Matrix.one_apply,apply_ite,ite_mul]

lemma symmetric_hs_power {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hs : P.IsSymm) (r : ℕ) :
    (∑ x, ∑ y, ((P^r) x y)^2) = ∑ x, (P^(2*r)) x x := by
  rw [two_mul,pow_add]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [(hs.pow r).apply x y,pow_two]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma trace_power_le_hs (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1)
    (r : ℕ) :
    (LinearMap.trace ℂ V ((A^(2*r+1)).toLinearMap)).re ≤
      ∑ j, ‖(A^r) (stdOrthonormalBasis ℂ V j)‖^2 := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_le_sum
  intro j _
  have he : (A^(2*r+1)) (B j) = (A^r) (A ((A^r) (B j))) := by
    have hnat : 2*r+1=r+(1+r) := by omega
    rw [hnat,pow_add,pow_add,pow_one]
    rfl
  change (inner ℂ (B j) ((A^(2*r+1)) (B j))).re ≤ ‖(A^r) (B j)‖^2
  rw [he]
  conv_lhs => rw [←(hs.pow r).adjoint_eq,ContinuousLinearMap.adjoint_inner_right]
  rw [(hs.pow r).adjoint_eq]
  apply (Complex.re_le_norm _).trans
  apply (norm_inner_le_norm _ _).trans
  have hh := A.le_opNorm ((A^r) (B j))
  have ha : ‖A ((A^r) (B j))‖ ≤ ‖(A^r) (B j)‖ := by
    exact hh.trans (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  nlinarith [norm_nonneg ((A^r) (B j))]

open UnitaryFinite
lemma palindrome_selfadjoint (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) : IsSelfAdjoint (sampleOperator ρ (palindromePerm d)) := by
  rw [sampleOperator_palindrome _ _ hρ]
  change IsSelfAdjoint (_ * star _)
  simp only [isSelfAdjoint_iff,star_mul,star_star]

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

lemma coefficient_trace_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (P : Matrix X X ℝ) (A : V →L[ℂ] V)
    (hmap : ∀ w, IsFixed a x₀ ρ w → ∀ v,
      DensityTransfer.applyKernel (fun x y => P x y) (normalizedCoefficient a x₀ ha ρ w v) =
        normalizedCoefficient a x₀ ha ρ w (A v))
    (hs : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V ((A^(2*r+1)).toLinearMap)).re ≤
      ∑ x, ∑ y, ((P^r) x y)^2 := by
  let W := fixedSpace a x₀ ρ
  let B := stdOrthonormalBasis ℂ V
  let C := stdOrthonormalBasis ℂ W
  let w : Fin (Module.finrank ℂ W) → V := fun i => (C i : V)
  have hfix (i) : IsFixed a x₀ ρ (w i) := (C i).2
  have hw : Orthonormal ℂ w := C.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  let v : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ V) → EuclideanSpace ℂ X :=
    fun ij => normalizedCoefficient a x₀ ha ρ (w ij.1) (B ij.2)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [v]
    rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix _) (hfix _)]
    rw [(orthonormal_iff_ite.mp hw), (orthonormal_iff_ite.mp B.orthonormal)]
    by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;>
      simp [h1,h2,Prod.ext_iff,eq_comm]
  have hp (s : ℕ) (i) (t : V) :
      DensityTransfer.applyKernel (fun x y => (P^s) x y) (normalizedCoefficient a x₀ ha ρ (w i) t) =
        normalizedCoefficient a x₀ ha ρ (w i) ((A^s) t) := by
    induction s with
    | zero => simp [applyKernel_one]
    | succ s ih =>
      rw [pow_succ',applyKernel_mul,ih,hmap _ (hfix _),pow_succ']
      rfl
  have hhs := DensityTransfer.hilbert_schmidt_family (fun x y => (P^r) x y) v hv
  have he : (∑ ij, ‖DensityTransfer.applyKernel (fun x y => (P^r) x y) (v ij)‖^2) =
      (Module.finrank ℂ W:ℝ) * ∑ j, ‖(A^r) (B j)‖^2 := by
    simp only [v,hp,normalizedCoefficient_norm a x₀ ha ρ hρ _ (hfix _)
      (hw.norm_eq_one _),Fintype.sum_prod_type]
    simp
  rw [he] at hhs
  exact (mul_le_mul_of_nonneg_left (trace_power_le_hs A hs hn r) (by positivity)).trans hhs

end Thorp.Casimir

namespace Thorp.Casimir
open scoped BigOperators Classical
open UnitaryFinite

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def tupleKernel (d k : ℕ) : Matrix (Fin k ↪ Card d) (Fin k ↪ Card d) ℝ :=
  fun x y => PairRouting.tupleProbability (palindromePerm d) x y

lemma palindrome_trace_amplification (d k : ℕ) (x₀ : Fin k ↪ Card d)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace tupleAction x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V (((sampleOperator ρ (palindromePerm d))^(2*r+1)).toLinearMap)).re ≤
    ∑ x, ∑ y, ((tupleKernel d k)^r) x y ^ 2 := by
  let ha := tupleAction_transitive x₀
  have hmap (w : V) (hw : IsFixed tupleAction x₀ ρ w) (v : V) :
      DensityTransfer.applyKernel (fun x y : Fin k ↪ Card d =>
        PairRouting.tupleProbability (palindromePerm d) x y)
        (normalizedCoefficient tupleAction x₀ ha ρ w v) =
      normalizedCoefficient tupleAction x₀ ha ρ w (sampleOperator ρ (palindromePerm d) v) := by
    have hh := coefficient_random tupleAction x₀ ha ρ hρ (palindromePerm d) w hw v
    have he : actionKernel tupleAction (palindromePerm d) =
        fun x y : Fin k ↪ Card d => PairRouting.tupleProbability (palindromePerm d) x y := by
      funext x y
      exact tupleAction_kernel _ x y
    rw [he,←sampleOperator_inv_apply,sampleOperator_inv _ hρ,
      (palindrome_selfadjoint d ρ hρ).adjoint_eq] at hh
    exact hh
  exact coefficient_trace_amplification tupleAction x₀ ha ρ hρ _ _ hmap
    (palindrome_selfadjoint d ρ hρ) (sampleOperator_norm_le ρ hρ _) r

end

lemma tupleKernel_symm (d k : ℕ) : (tupleKernel d k).IsSymm := by
  ext x y
  exact palindrome_kernel_symmetric d y x

lemma tupleKernel_power64 (d k : ℕ) (x y : Fin k ↪ Card d) :
    ((tupleKernel d k)^64) x y ≤
      Real.exp ((64*(1+heightDecay 1))*k)/(Fintype.card (Fin k ↪ Card d):ℝ) := by
  let : Nonempty (Fin k ↪ Card d) := ⟨x⟩
  have hr (x : Fin k ↪ Card d) : ∑ y, tupleKernel d k x y = 1 :=
    PairRouting.tupleProbability_row_sum _ x
  have hc (y : Fin k ↪ Card d) : ∑ x, tupleKernel d k x y = 1 := by
    simp_rw [(tupleKernel_symm d k).apply y]
    exact hr y
  have hm (x : Fin k ↪ Card d) :
      finiteMean (fun y => ((Fintype.card (Fin k ↪ Card d):ℝ)*tupleKernel d k x y)^
        (1+(1/32:ℝ))) ≤ Real.exp ((k:ℝ)*(1+heightDecay 1)) := by
    simpa only [palindromeRowMoment,Fintype.card_fin,tupleKernel] using
      row_moment_coarse d x (1/32) (by norm_num) (by norm_num)
  have hnum : 2 ≤ (1+(1/32:ℝ))^(32:ℕ) := by
    have hh := one_add_mul_le_pow (a := (1/32:ℝ)) (by norm_num) 32
    norm_num at hh ⊢
  have hh := StrongSmoothing.symmetric_kernel_smoothing (tupleKernel d k)
    (fun x y => PairRouting.tupleProbability_nonneg _ x y) hr hc (tupleKernel_symm d k)
    (p := 1+(1/32:ℝ)) (A := k*(1+heightDecay 1)) (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [heightDecay_nonneg 1])) hm 32 hnum x y
  have he : 2*((k:ℝ)*(1+heightDecay 1))*(32:ℝ) = (64*(1+heightDecay 1))*k := by ring
  simpa only [show 2*32=64 by norm_num,Nat.cast_ofNat,he] using hh

lemma K_selfadjoint (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    @IsSelfAdjoint _ (ContinuousLinearMap.instStarId (𝕜:=ℂ) (E:=Specht.hilbertSpace μ)) (K d μ e) := by
  exact palindrome_selfadjoint (V:=Specht.hilbertSpace μ) d _ (Specht.relabelledUnitary_unitary μ e)

lemma K_norm_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    ‖K d μ e‖ ≤ 1 :=
  sampleOperator_norm_le _ (Specht.relabelledUnitary_unitary μ e) _

lemma fixed_trace_bound (d k : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (x₀ : Fin k ↪ Card d) :
    (Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
      (Specht.relabelledUnitary μ e)):ℝ) * traceMoment d μ e 65 ≤
        Real.exp ((64*(1+heightDecay 1))*k) := by
  let ρ := Specht.relabelledUnitary μ e
  let := Specht.relabelledUnitary_irreducible μ e
  have hh := palindrome_trace_amplification (V:=Specht.hilbertSpace μ) d k x₀ ρ
    (Specht.relabelledUnitary_unitary μ e) 32
  change _ * traceMoment d μ e 65 ≤ _ at hh
  rw [symmetric_hs_power _ (tupleKernel_symm d k)] at hh
  apply hh.trans
  have hX : (0:ℝ) < Fintype.card (Fin k ↪ Card d) := by
    let : Nonempty (Fin k ↪ Card d) := ⟨x₀⟩
    exact Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ ≤ ∑ x : Fin k ↪ Card d,
        Real.exp ((64*(1+heightDecay 1))*k)/(Fintype.card (Fin k ↪ Card d):ℝ) :=
      Finset.sum_le_sum (fun x _ => tupleKernel_power64 d k x x)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_div_cancel₀ _ (ne_of_gt hX)

lemma levelScale_ge (n k : ℕ) (hk : k ≤ n) : (k:ℝ) ≤ levelScale n k := by
  by_cases h : k=0
  · simp [h,levelScale]
  have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero h
  have hlog : 0 ≤ Real.log ((n:ℝ)/k) := Real.log_nonneg ((one_le_div hkp).mpr (by exact_mod_cast hk))
  dsimp [levelScale]
  nlinarith

lemma choose_le_exp_levelScale (n k : ℕ) (hn : 0<n) (hk : k≤n) :
    (n.choose k:ℝ) ≤ Real.exp (levelScale n k) := by
  by_cases h : k=0
  · simp [h,levelScale]
  have hkp : 0<k := Nat.pos_of_ne_zero h
  have hh := DimensionEstimates.log_choose_upper n k hn hk
  have hf := DimensionEstimates.log_factorial_lower k hkp
  have he : Real.log ((n:ℝ)/k) = Real.log n-Real.log k :=
    Real.log_div (by positivity) (by positivity)
  have hl : Real.log (n.choose k:ℝ) ≤ levelScale n k := by
    dsimp [levelScale]
    rw [he]
    linarith
  rw [←Real.exp_log (by exact_mod_cast Nat.choose_pos hk : (0:ℝ)<n.choose k)]
  exact Real.exp_le_exp.mpr hl

lemma trace_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    (Module.finrank ℂ (Specht.space μ):ℝ)*traceMoment d μ e 65 ≤
      Real.exp ((1+64*(1+heightDecay 1))*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  let k := μ.card-μ.rowLen 0
  have hn : μ.card=2^d := by
    rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hk : k≤2^d := by dsimp [k]; omega
  let x₀ : Fin k ↪ Card d := (Fin.castLEEmb (show k≤Fintype.card (Card d) by simpa [card_positions] using hk)).trans
    (Fintype.equivFin (Card d)).symm.toEmbedding
  let m := Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
    (Specht.relabelledUnitary μ e))
  have hd : (Module.finrank ℂ (Specht.space μ):ℝ) ≤ (m:ℝ)*((2^d).choose k:ℝ) := by
    have hh := Specht.relabelled_tuple_dimension μ e x₀
    simp only [Fintype.card_fin] at hh
    change Module.finrank ℂ (Specht.hilbertSpace μ) * k.choose k ≤ m * μ.card.choose k at hh
    rw [Nat.choose_self,mul_one,Specht.finrank_hilbertSpace,hn] at hh
    exact_mod_cast hh
  have hm := fixed_trace_bound d k μ e x₀
  by_cases ht : 0≤traceMoment d μ e 65
  · calc
      _ ≤ ((m:ℝ)*((2^d).choose k:ℝ))*traceMoment d μ e 65 :=
        mul_le_mul_of_nonneg_right hd ht
      _ = ((2^d).choose k:ℝ)*((m:ℝ)*traceMoment d μ e 65) := by ring
      _ ≤ ((2^d).choose k:ℝ)*Real.exp ((64*(1+heightDecay 1))*k) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ Real.exp (levelScale (2^d) k)*Real.exp ((64*(1+heightDecay 1))*levelScale (2^d) k) := by
        apply mul_le_mul (choose_le_exp_levelScale _ _ (by positivity) hk) _ (by positivity) (Real.exp_nonneg _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (levelScale_ge _ _ hk) (by linarith [heightDecay_nonneg 1])
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge ht)).trans (Real.exp_nonneg _)

end Thorp.Casimir

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter UnitaryFinite DimensionEstimates

lemma levelScale_le (n k : ℕ) (hn : 0<n) (_ : k≤n) : levelScale n k ≤ n := by
  by_cases hz : k=0
  · simp [hz,levelScale]
  have hkp : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hh := Real.log_le_sub_one_of_pos (div_pos hnp hkp)
  have hm := mul_le_mul_of_nonneg_left hh hkp.le
  have he : (k:ℝ)*((n:ℝ)/k)=n := mul_div_cancel₀ _ (ne_of_gt hkp)
  dsimp [levelScale]
  nlinarith

lemma nontrivial_uniform_zero (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 0<μ.card-μ.rowLen 0) :
    uniformOperator (V:=Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e)=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply SparseContact.point_relabelled_fixed_zero μ e ∅ (by simpa using hk)
  intro g _
  have he := congrArg (fun A : Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ => A v)
    (uniformOperator_left (V:=Specht.hilbertSpace μ) (Specht.relabelledUnitary μ e) g)
  exact he

lemma gap_of_uniform_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) (hz : uniformOperator ρ=0) :
    ‖sampleOperator ρ (palindromePerm d)‖ ≤ blockGap d := by
  have hh := palindrome_off_invariants_gap d ρ hρ
  rw [hz,sub_zero,←sampleOperator_weighted] at hh
  exact hh

lemma nontrivial_gap (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : 0<μ.card-μ.rowLen 0) : ‖K d μ e‖ ≤ blockGap d := by
  exact gap_of_uniform_zero (V:=Specht.hilbertSpace μ) d _
    (Specht.relabelledUnitary_unitary μ e) (nontrivial_uniform_zero d μ e hk)

lemma eventual_level_dimension :
    ∃ η : ℝ, 0<η ∧ ∀ᶠ d : ℕ in atTop,
      ∀ μ : YoungDiagram, μ.card=2^d → 0<μ.card-μ.rowLen 0 →
        (μ.colLen 0:ℝ)≤(μ.card:ℝ)/2 →
        η*levelScale (2^d) (μ.card-μ.rowLen 0) ≤
          Real.log (Module.finrank ℂ (Specht.space μ)) := by
  obtain ⟨h,hh,hm⟩ := Specht.medium_dimension (1/16) (by norm_num) (by norm_num)
  refine ⟨min (1/3) h,lt_min (by norm_num) hh,?_⟩
  filter_upwards [twopow_nat_tendsto.eventually hm] with d hd
  intro μ hμ hk hc
  let k := μ.card-μ.rowLen 0
  have hkn : k≤2^d := by dsimp [k]; omega
  have hΛ : 0≤levelScale (2^d) k := (Nat.cast_nonneg k).trans (levelScale_ge _ _ hkn)
  have hr : ((μ.card-μ.rowLen 0:ℕ):ℝ)=(μ.card:ℝ)-μ.rowLen 0 :=
    Nat.cast_sub (Specht.rowLen_zero_le_card μ)
  by_cases hs : (k:ℝ)≤(2^d:ℕ)/16
  · have hk2 : 2*k≤2^d := by exact_mod_cast (show (2:ℝ)*k≤(2^d:ℕ) by linarith)
    have hdim := DimensionEstimates.near_row_log_dimension (2^d) k _ hk hk2
      (by simpa only [←hμ] using Specht.choose_tail_le_dimension μ)
    have hkp : (0:ℝ)<k := by exact_mod_cast hk
    have hratio : (16:ℝ)≤(2^d:ℕ)/k := (le_div_iff₀ hkp).mpr (by linarith)
    have hlog : 4*Real.log 2 ≤ Real.log ((2^d:ℕ)/k) := by
      have ht := Real.log_le_log (by norm_num : (0:ℝ)<16) hratio
      rw [show (16:ℝ)=2^(4:ℕ) by norm_num,Real.log_pow] at ht
      simpa using ht
    have hlog2 : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hL : levelScale (2^d) k ≤ 3*Real.log (Module.finrank ℂ (Specht.space μ)) := by
      dsimp [levelScale]
      nlinarith
    have hη := mul_le_mul_of_nonneg_right (min_le_left (1/3:ℝ) h) hΛ
    nlinarith
  · have hdim := hd μ hμ (by rw [←hμ,←hr]; change (1/16:ℝ)*(μ.card:ℝ)≤(k:ℝ); rw [hμ]; linarith)
      (by simpa only [←hμ] using hc)
    have hL := levelScale_le (2^d) k (by positivity) hkn
    have ht := mul_le_mul_of_nonneg_left hL hh.le
    have hη := mul_le_mul_of_nonneg_right (min_le_right (1/3:ℝ) h) hΛ
    nlinarith

lemma eventual_level_contraction :
    ∃ a : ℝ, 0<a ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ), 0<μ.card-μ.rowLen 0 →
        ‖K d μ e‖ ≤ Real.exp (-a*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  obtain ⟨a,h,ha,hh,hsp⟩ := Specht.spectral_regimes
  obtain ⟨η,hη,hdim⟩ := eventual_level_dimension
  refine ⟨a*η,mul_pos ha hη,?_⟩
  filter_upwards [hsp,hdim,eventually_ge_atTop 1] with d hs hd hd1
  intro μ e hk
  by_cases ht : (μ.card:ℝ)/2 < μ.colLen 0
  · have hz := Specht.palindrome_tall_zero_general d (by omega) μ e ht
    change K d μ e=0 at hz
    rw [hz,@norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _]
    exact (Real.exp_pos _).le
  · have hc := le_of_not_gt ht
    have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
    apply (hs μ e hk hc).1.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hd μ hμ hk hc) ha.le
    nlinarith

lemma finite_positive_lower (f : ℕ → ℝ) (D : ℕ) (hf : ∀ d<D,0<f d) :
    ∃ b : ℝ, 0<b ∧ ∀ d<D,b≤f d := by
  induction D with
  | zero => exact ⟨1,by norm_num,by omega⟩
  | succ D ih =>
    obtain ⟨b,hb,hh⟩ := ih (fun d hd => hf d (by omega))
    refine ⟨min b (f D),lt_min hb (hf D (by omega)),?_⟩
    intro d hd
    by_cases he : d=D
    · subst d; exact min_le_right _ _
    · exact (min_le_left _ _).trans (hh d (by omega))

theorem level_contraction :
    ∃ a : ℝ, 0<a ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
        ‖K d μ e‖ ≤ Real.exp (-a*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  obtain ⟨a,ha,he⟩ := eventual_level_contraction
  obtain ⟨D,hD⟩ := eventually_atTop.mp he
  let f (d : ℕ) : ℝ := -Real.log (blockGap d)/(2:ℝ)^d
  have hf (d : ℕ) : 0<f d := by
    have hl := Real.log_neg (blockGap_pos d) (blockGap_lt_one d)
    exact div_pos (neg_pos.mpr hl) (by positivity)
  obtain ⟨b,hb,hbD⟩ := finite_positive_lower f D (fun d _ => hf d)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro d μ e hk
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hkn : μ.card-μ.rowLen 0≤2^d := by omega
  have hΛ : 0≤levelScale (2^d) (μ.card-μ.rowLen 0) :=
    (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
  by_cases hd : D≤d
  · apply (hD d hd μ e hk).trans (Real.exp_le_exp.mpr _)
    have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hΛ
    linarith
  · have hab : min a b≤f d := (min_le_right _ _).trans (hbD d (by omega))
    have hscale : levelScale (2^d) (μ.card-μ.rowLen 0) ≤ (2:ℝ)^d := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using levelScale_le (2^d) _ (by positivity) hkn
    have hprod := mul_le_mul_of_nonneg_right hab (by positivity : (0:ℝ)≤(2:ℝ)^d)
    have hfprod : f d*(2:ℝ)^d = -Real.log (blockGap d) := by dsimp [f]; field_simp
    rw [hfprod] at hprod
    have hs := mul_le_mul_of_nonneg_left hscale (le_of_lt (lt_min ha hb))
    calc
      _ ≤ blockGap d := nontrivial_gap d μ e hk
      _ = Real.exp (Real.log (blockGap d)) := (Real.exp_log (blockGap_pos d)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Thorp.Casimir

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite

noncomputable def cardLabels (d : ℕ) (μ : Shapes (2^d)) : Card d ≃ Cell μ.1 :=
  ((Fintype.equivFin (Card d)).trans (finCongr (card_positions d))).trans (labels μ).symm

noncomputable def cardRepresentation (d : ℕ) (μ : Shapes (2^d)) :
    Representation ℂ (Equiv.Perm (Card d)) (hilbertSpace μ.1) :=
  relabelledUnitary μ.1 (cardLabels d μ)

lemma cardRepresentation_unitary (d : ℕ) (μ : Shapes (2^d)) :
    IsUnitary (V := hilbertSpace μ.1) (cardRepresentation d μ) :=
  relabelledUnitary_unitary _ _

noncomputable instance cardRepresentation_irreducible (d : ℕ) (μ : Shapes (2^d)) :
    Representation.IsIrreducible (cardRepresentation d μ) :=
  relabelledUnitary_irreducible _ _

lemma relabelledUnitary_neq {α : Type*} (μ ν : YoungDiagram)
    (e : α ≃ Cell μ) (f : α ≃ Cell ν)
    (T : Representation.Equiv (relabelledUnitary μ e) (relabelledUnitary ν f)) : μ=ν := by
  let S := (spaceHilbertEquiv μ).trans (T.toLinearEquiv.trans (spaceHilbertEquiv ν).symm)
  apply shapes_eq_of_equivariant_equiv μ ν (e.symm.trans f) S
  intro p v
  have hT := Representation.IntertwiningMap.isIntertwining _ _ T.toIntertwiningMap
    (e.symm.permCongr p) (spaceHilbertEquiv μ v)
  change T.toLinearEquiv (spaceHilbertEquiv μ
    (representation μ (e.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv μ).symm (spaceHilbertEquiv μ v))))=
    spaceHilbertEquiv ν (representation ν (f.permCongr (e.symm.permCongr p))
      ((spaceHilbertEquiv ν).symm (T.toLinearEquiv (spaceHilbertEquiv μ v)))) at hT
  have he : e.permCongr (e.symm.permCongr p)=p := by
    apply Equiv.ext
    intro x
    simp only [Equiv.permCongr_apply,Equiv.symm_symm,e.apply_symm_apply]
  have hf : f.permCongr (e.symm.permCongr p)=(e.symm.trans f).permCongr p := by
    apply Equiv.ext
    intro x
    rfl
  rw [he,hf,LinearEquiv.symm_apply_apply] at hT
  have ht := congrArg (spaceHilbertEquiv ν).symm hT
  simpa only [LinearEquiv.symm_apply_apply,S,LinearEquiv.trans_apply] using ht

lemma cardRepresentation_distinct (d : ℕ) (μ ν : Shapes (2^d)) (hne : μ≠ν) :
    ¬Nonempty (Representation.Equiv (cardRepresentation d μ) (cardRepresentation d ν)) := by
  rintro ⟨T⟩
  exact hne (Subtype.ext (relabelledUnitary_neq μ.1 ν.1 (cardLabels d μ) (cardLabels d ν) T))

lemma card_conjugacy_shapes (d : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Card d)))≤Fintype.card (Shapes (2^d)) := by
  have h := Nat.card_le_card_of_injective _ (conjugacyPartition_injective (α := Card d))
  simpa only [card_positions,Nat.card_eq_fintype_card,Fintype.card_congr (shapePartitionEquiv (2^d))] using h

lemma row_zero_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) (x : Cell μ) : row x=0 := by
  have hr : μ.row 0=μ.cells := Finset.eq_of_subset_of_card_le
    (Finset.filter_subset _ _) (by rw [←μ.rowLen_eq_card]; exact hμ.ge)
  have hx : x.1∈μ.row 0 := by rw [hr]; exact x.2
  exact (YoungDiagram.mem_row_iff.mp hx).2

lemma tabloid_subsingleton_of_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card) :
    Subsingleton (Tabloid μ) := by
  refine ⟨fun f g => ?_⟩
  apply Subtype.ext
  funext x
  obtain ⟨p,hp⟩ := f.2
  obtain ⟨q,hq⟩ := g.2
  simp only [hp,hq,Function.comp_apply]
  apply Fin.ext
  exact (row_zero_of_full_row μ hμ (p x)).trans (row_zero_of_full_row μ hμ (q x)).symm

lemma representation_full_row (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (p : Equiv.Perm (Cell μ)) : representation μ p=1 := by
  let := tabloid_subsingleton_of_full_row μ hμ
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext f
  change v.1 (tabloidAct p⁻¹ f)=v.1 f
  rw [show tabloidAct p⁻¹ f=f from Subsingleton.elim _ _]

lemma relabelled_full_row {α : Type*} (μ : YoungDiagram) (hμ : μ.rowLen 0=μ.card)
    (e : α ≃ Cell μ) (p : Equiv.Perm α) : relabelledUnitary μ e p=1 := by
  change ((spaceHilbertEquiv μ).conjAlgEquiv ℂ) (representation μ (e.permCongr p))=1
  rw [representation_full_row μ hμ,map_one]

end Thorp.Specht
namespace Thorp.UnitaryFinite
open scoped BigOperators Classical
variable {G Ω V : Type*} [Group G] [Fintype G] [Fintype Ω] [Nonempty Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sample_uniform_left (ρ : Representation ℂ G V) (P : Ω → G) :
    sampleOperator ρ P*uniformOperator ρ=uniformOperator ρ := by
  rw [sampleOperator_weighted,weighted_uniform_left,sampleLaw_sum,one_smul]

lemma uniform_zero_of_sample_norm_lt_one (ρ : Representation ℂ G V) (P : Ω → G)
    (h : ‖sampleOperator ρ P‖<1) : uniformOperator ρ=0 := by
  have hn := norm_mul_le (sampleOperator ρ P) (uniformOperator ρ)
  rw [sample_uniform_left] at hn
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (uniformOperator ρ)]

omit [Fintype G] in
lemma sampleOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) (P : Ω → G) :
    sampleOperator ρ P=1 := by
  convert sampleOperator_one (Ω := Ω) ρ using 1
  unfold sampleOperator
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  apply ContinuousLinearMap.ext
  intro v
  change ρ (P ω) v=ρ 1 v
  rw [hρ,hρ]

lemma uniformOperator_trivial (ρ : Representation ℂ G V) (hρ : ∀ g,ρ g=1) :
    uniformOperator ρ=1 := by
  rw [←sampleOperator_uniform]
  exact sampleOperator_trivial ρ hρ id

lemma weighted_sub (ρ : Representation ℂ G V) (p q : G → ℝ) :
    weightedOperator ρ (fun g => p g-q g)=weightedOperator ρ p-weightedOperator ρ q := by
  simp only [weightedOperator,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]

end Thorp.UnitaryFinite

namespace Thorp
open scoped BigOperators Classical
open UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma physical_palindrome_norm (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d d)‖^2=‖sampleOperator ρ (palindromePerm d)‖ := by
  rw [physical_sweep_adjoint d ρ hρ,sampleOperator_palindrome d ρ hρ]
  have h := ContinuousLinearMap.norm_adjoint_comp_self
    ((sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint)
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  simpa only [ContinuousLinearMap.mul_def,←sq] using h.symm

lemma physical_power_bound (d C : ℕ) (hC : 0 < C) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    ‖sampleOperator ρ (run d (C*d))‖^2≤‖sampleOperator ρ (palindromePerm d)‖^C := by
  have he : sampleOperator ρ (run d (C*d))=(sampleOperator ρ (run d d))^C := by
    simp only [sampleOperator_run,←pow_mul,Nat.mul_comm C d]
  rw [he,←physical_palindrome_norm d ρ hρ]
  calc
    _ ≤ (‖sampleOperator ρ (run d d)‖^C)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pow_le' _ hC) _
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm C 2]

end Thorp
namespace Thorp.Specht
open scoped BigOperators Classical

section
open UnitaryFinite

lemma card_fourier_decay (d C : ℕ) (μ : Shapes (2^d)) (a s : ℝ)
    (ha : 0 < a) (hs : 0 ≤ s) (hC : s+2 ≤ a*C)
    (hD : 1≤Real.log (Module.finrank ℂ (space μ.1)))
    (hK : ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (palindromePerm d)‖≤
      Real.exp (-a*Real.log (Module.finrank ℂ (space μ.1)))) :
    (Module.finrank ℂ (hilbertSpace μ.1):ℝ)^2*
      ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d (C*d))-uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2≤
        Real.exp (-s*Real.log (Module.finrank ℂ (space μ.1))) := by
  let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
  have hu : uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)=0 :=
    uniform_zero_of_sample_norm_lt_one _ (palindromePerm d) (hK.trans_lt (by
      rw [Real.exp_lt_one_iff]; nlinarith))
  rw [hu,sub_zero,finrank_hilbertSpace]
  have hCp : 0 < C := by
    by_contra hn
    have hz : C=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hC
    linarith
  have hp := physical_power_bound d C hCp (cardRepresentation d μ) (cardRepresentation_unitary d μ)
  have hkpow := pow_le_pow_left₀ (norm_nonneg _) hK C
  have hDp : (0:ℝ)<Module.finrank ℂ (space μ.1) := by exact_mod_cast dimension_pos μ.1
  calc
    _ ≤ (Module.finrank ℂ (space μ.1):ℝ)^2*
        (Real.exp (-a*Real.log (Module.finrank ℂ (space μ.1))))^C :=
      mul_le_mul_of_nonneg_left (hp.trans hkpow) (sq_nonneg _)
    _ = Real.exp ((2-a*C)*Real.log (Module.finrank ℂ (space μ.1))) := by
      rw [←Real.exp_log hDp,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma card_fourier_tall (d C : ℕ) (hd : 0<d) (hC : 0<C) (μ : Shapes (2^d))
    (hc : (μ.1.card:ℝ)/2<(μ.1.colLen 0:ℝ)) :
    sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d (C*d))-uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)=0 := by
  let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
  let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
  let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
  have hk : sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (palindromePerm d)=0 :=
    palindrome_tall_zero_general d hd μ.1 (cardLabels d μ) hc
  have hu : uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)=0 :=
    uniform_zero_of_sample_norm_lt_one _ (palindromePerm d) (by rw [hk,norm_zero]; norm_num)
  rw [hu,sub_zero]
  apply norm_eq_zero.mp
  have hp := physical_power_bound d C hC (cardRepresentation d μ) (cardRepresentation_unitary d μ)
  rw [hk,norm_zero,zero_pow (by omega : C≠0)] at hp
  nlinarith [norm_nonneg (sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d (C*d)))]

lemma card_fourier_full_row (d t : ℕ) (μ : Shapes (2^d)) (hj : μ.1.card-μ.1.rowLen 0=0) :
    sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t)-uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)=0 := by
  have hr : μ.1.rowLen 0=μ.1.card := by have := rowLen_zero_le_card μ.1; omega
  have ht (p : Equiv.Perm (Card d)) : cardRepresentation d μ p=1 :=
    relabelled_full_row μ.1 hr (cardLabels d μ) p
  rw [sampleOperator_trivial _ ht,uniformOperator_trivial _ ht,sub_self]

end

lemma half_geom_sum (n : ℕ) : (∑ j∈Finset.range n,(1/2:ℝ)^j)≤2 := by
  have he : (∑ j∈Finset.range n,(1/2:ℝ)^j)=2*(1-(1/2:ℝ)^n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]

lemma shape_weight_sum (N : ℕ) :
    (∑ μ : Shapes N,(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0))≤2 := by
  have he := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Shapes N))) (t := Finset.range (N+1))
    (g := fun μ : Shapes N => μ.1.card-μ.1.rowLen 0)
    (by intro μ _; simp only [Finset.mem_range]; have := μ.2; omega)
    (fun j => (1/4:ℝ)^j)
  rw [←he]
  apply le_trans _ (half_geom_sum (N+1))
  apply Finset.sum_le_sum
  intro j _
  have hc : ((Finset.univ.filter (fun μ : Shapes N => μ.1.card-μ.1.rowLen 0=j)).card:ℝ)≤(2:ℝ)^j := by
    have hh := tail_shapes_count N j
    rw [Fintype.card_subtype] at hh
    exact_mod_cast hh
  simp only [Finset.sum_const,nsmul_eq_mul]
  calc
    _ ≤ (2:ℝ)^j*(1/4:ℝ)^j := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1/2:ℝ)^j := by rw [←mul_pow]; norm_num

lemma near_shape_term (N j : ℕ) (L s : ℝ) (hN : 0<N) (hs : 4≤ s)
    (hL : 0≤L) (hl : (1/2:ℝ)*Real.log N≤L) (hj : (j:ℝ)≤L) :
    Real.exp (-s*L)≤(1/(N:ℝ))*(1/4:ℝ)^j := by
  have hlog : Real.log (4:ℝ)≤2 := by
    have h2 : Real.log (2:ℝ)<1 := by
      have ht := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
      norm_num at ht
      exact ht
    have he : Real.log (4:ℝ)=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    linarith
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ Real.exp (-(Real.log N+(j:ℝ)*Real.log 4)) := Real.exp_le_exp.mpr (by
      have hb := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j : (0:ℝ)≤j)
      nlinarith)
    _ = _ := by
      rw [neg_add,Real.exp_add,Real.exp_neg,Real.exp_log hnR,one_div]
      congr 1
      rw [show -((j:ℝ)*Real.log (4:ℝ))=(j:ℝ)*(-Real.log 4) by ring,
        Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]
      norm_num

lemma shapes_medium_sum (N : ℕ) (h s : ℝ) (hsh : 2≤ s*h) :
    (Fintype.card (Shapes N):ℝ)*Real.exp (-s*h*N)≤Real.exp (-(N:ℝ)) := by
  have hc : (Fintype.card (Shapes N):ℝ)≤(2:ℝ)^N := by exact_mod_cast shapes_count N
  have hl : Real.log (2:ℝ)≤1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  calc
    _ ≤ (2:ℝ)^N*Real.exp (-s*h*N) := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = Real.exp ((Real.log 2-s*h)*N) := by
      rw [←Real.exp_log (by norm_num : (0:ℝ)<2),←Real.exp_nat_mul,←Real.exp_add,Real.log_exp]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hb := mul_le_mul_of_nonneg_right (show Real.log 2-s*h≤-1 by linarith) (Nat.cast_nonneg N : (0:ℝ)≤N)
      linarith)

end Thorp.Specht

namespace Thorp
open scoped BigOperators Classical

section
open UnitaryFinite Specht DimensionEstimates Filter

lemma sampleLaw_run (d t : ℕ) : sampleLaw (run d t)=law d t := by
  classical
  funext g
  unfold sampleLaw finiteMean law
  rw [Fintype.card_subtype]
  apply congrArg (fun z : ℝ => z/(Fintype.card (Fin t → Coins d):ℝ))
  convert Finset.sum_boole (R := ℝ) (fun x => run d t x = g) Finset.univ using 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with h <;> simp only [h, ite_true, ite_false]

lemma physical_fourier_bound (d t : ℕ) :
    distance d t^2≤∑ μ : Shapes (2^d),(Module.finrank ℂ (hilbertSpace μ.1):ℝ)^2*
      ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t)-
        uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2 := by
  let V : Shapes (2^d) → Type := fun μ => hilbertSpace μ.1
  let : ∀ μ,NormedAddCommGroup (V μ) := fun _ => inferInstance
  let : ∀ μ,InnerProductSpace ℂ (V μ) := fun _ => inferInstance
  let : ∀ μ,FiniteDimensional ℂ (V μ) := fun _ => inferInstance
  let p := fun g : Equiv.Perm (Card d) => law d t g-1/(Nat.factorial (2^d):ℝ)
  have hb := FiniteFourier.l1_fourier_bound V (cardRepresentation d)
    (cardRepresentation_unitary d) (cardRepresentation_distinct d) (card_conjugacy_shapes d) p
  have he (μ : Shapes (2^d)) : weightedOperator (V := V μ) (cardRepresentation d μ) p=
      sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t)-
        uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) := by
    rw [sampleOperator_weighted,sampleLaw_run]
    dsimp only [p]
    rw [weighted_sub]
    congr 1
    unfold uniformOperator
    rw [card_permutations]
    simp only [one_div]
  simp_rw [he] at hb
  apply le_trans _ hb
  change ((1/2:ℝ)*(∑ g,|p g|))^2≤(∑ g,|p g|)^2
  nlinarith [sq_nonneg (∑ g,|p g|)]

theorem eventual_physical_bound :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ d : ℕ in atTop,
      distance d (C*d)^2≤2/(2:ℝ)^d+Real.exp (-(2:ℝ)^d) := by
  obtain ⟨a,h,ha,hh,hreg⟩ := spectral_regimes
  let s := max 4 (2/h)
  have hs4 : 4≤ s := le_max_left _ _
  have hs : 0≤ s := by dsimp [s]; positivity
  have hsh : 2≤ s*h := by
    have hc := le_max_right (4:ℝ) (2/h)
    exact (div_le_iff₀ hh).mp hc
  obtain ⟨C,hC₀⟩ := exists_nat_ge ((s+2)/a)
  have hC : s+2≤a*C := by
    have hC := (div_le_iff₀ ha).mp hC₀
    nlinarith
  have hCp : 0<C := by
    by_contra hn
    have hz : C=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hC
    linarith
  refine ⟨C,hCp,?_⟩
  filter_upwards [hreg,eventually_gt_atTop 0] with d hd hdp
  have hbound (μ : Shapes (2^d)) :
      (Module.finrank ℂ (hilbertSpace μ.1):ℝ)^2*
        ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d (C*d))-
          uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2≤
        (1/(2:ℝ)^d)*(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0)+Real.exp (-s*h*(2:ℝ)^d) := by
    let : NormedAddCommGroup (hilbertSpace μ.1) := inferInstance
    let : InnerProductSpace ℂ (hilbertSpace μ.1) := inferInstance
    let : FiniteDimensional ℂ (hilbertSpace μ.1) := inferInstance
    have hr : 0≤(1/(2:ℝ)^d)*(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0) := by positivity
    by_cases hj : μ.1.card-μ.1.rowLen 0=0
    · rw [card_fourier_full_row d (C*d) μ hj,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]
      positivity
    by_cases hc : (μ.1.colLen 0:ℝ)≤(μ.1.card:ℝ)/2
    · obtain ⟨hK,hD,halt⟩ := hd μ.1 (cardLabels d μ) (by omega) hc
      have ht := card_fourier_decay d C μ a s ha hs hC hD hK
      apply ht.trans
      rcases halt with ⟨hlog,hjlog⟩ | hlog
      · have hnear := near_shape_term μ.1.card (μ.1.card-μ.1.rowLen 0)
          (Real.log (Module.finrank ℂ (space μ.1))) s
          (by rw [μ.2]; positivity) hs4 (by linarith) hlog hjlog
        rw [μ.2,Nat.cast_pow,Nat.cast_ofNat] at hnear
        rw [μ.2]
        exact hnear.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      · apply le_trans (b := Real.exp (-s*h*(2:ℝ)^d)) _ (le_add_of_nonneg_left hr)
        apply Real.exp_le_exp.mpr
        nlinarith
    · rw [card_fourier_tall d C hdp hCp μ (lt_of_not_ge hc),norm_zero,
        zero_pow (by norm_num : 2≠0),mul_zero]
      positivity
  calc
    _ ≤ ∑ μ : Shapes (2^d),(Module.finrank ℂ (hilbertSpace μ.1):ℝ)^2*
        ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d (C*d))-
          uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2 := physical_fourier_bound d (C*d)
    _ ≤ ∑ μ : Shapes (2^d),((1/(2:ℝ)^d)*(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0)+
        Real.exp (-s*h*(2:ℝ)^d)) := Finset.sum_le_sum (fun μ _ => hbound μ)
    _ = (1/(2:ℝ)^d)*(∑ μ : Shapes (2^d),(1/4:ℝ)^(μ.1.card-μ.1.rowLen 0))+
        (Fintype.card (Shapes (2^d)):ℝ)*Real.exp (-s*h*(2:ℝ)^d) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (1/(2:ℝ)^d)*2+Real.exp (-(2:ℝ)^d) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (shape_weight_sum (2^d)) (by positivity)
      · simpa only [Nat.cast_pow,Nat.cast_ofNat] using shapes_medium_sum (2^d) h s hsh
    _ = _ := by ring

end
open Filter DimensionEstimates

lemma physical_convergence : ∃ C : ℕ, 0<C ∧
    Tendsto (fun d : ℕ => distance d (C*d)) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := eventual_physical_bound
  refine ⟨C,hC,?_⟩
  have hrec : Tendsto (fun d : ℕ => 2/(2:ℝ)^d) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop twopow_tendsto
  have hexp : Tendsto (fun d : ℕ => Real.exp (-(2:ℝ)^d)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp twopow_tendsto
  have hr : Tendsto (fun d : ℕ => 2/(2:ℝ)^d+Real.exp (-(2:ℝ)^d)) atTop (nhds 0) := by
    simpa only [zero_add] using hrec.add hexp
  have hsq : Tendsto (fun d : ℕ => distance d (C*d)^2) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun d => sq_nonneg (distance d (C*d)))) hbound hr
  have hs := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hsq
  have he : (Real.sqrt ∘ fun d : ℕ => distance d (C*d)^2)=(fun d => distance d (C*d)) := by
    funext d
    exact Real.sqrt_sq (distance_nonneg _ _)
  rw [he,Real.sqrt_zero] at hs
  exact hs

end Thorp

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter UnitaryFinite

lemma K_source_square (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    K d μ e = (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=Specht.hilbertSpace μ) (F:=Specht.hilbertSpace μ)
      (SparseContact.sweepOperator d μ e true)) *
      SparseContact.sweepOperator d μ e true := by
  simp only [SparseContact.sweepOperator,ite_true]
  rw [sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),
    ContinuousLinearMap.adjoint_adjoint]
  exact sampleOperator_palindrome _ _ (Specht.relabelledUnitary_unitary μ e)

lemma density_bound (d k : ℕ) (hk : k≤2^d) (x : Fin k ↪ Card d) :
    (palindromeRowMoment d x (1/64))^(64/65:ℝ) ≤
      Real.exp ((1+64*(1+heightDecay 1))*levelScale (2^d) k) := by
  have hm := row_moment_coarse d x (1/64) (by norm_num) (by norm_num)
  have hh := Real.rpow_le_rpow (palindromeRowMoment_nonneg d x (1/64)) hm
    (by norm_num : (0:ℝ)≤64/65)
  simp only [Fintype.card_fin] at hh
  apply hh.trans
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hL := levelScale_ge (2^d) k hk
  have hA := heightDecay_nonneg 1
  have hk0 : (0:ℝ)≤k := by positivity
  nlinarith

lemma fromDistance_eq (d t : ℕ) (σ : Equiv.Perm (Card d)) : fromDistance d t σ=distance d t := by
  unfold fromDistance distance
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ (fun _ => rfl)

lemma trace_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (hA : IsSelfAdjoint A) :
    (((LinearMap.trace ℂ V A.toLinearMap).re : ℝ):ℂ) = LinearMap.trace ℂ V A.toLinearMap := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum,Complex.ofReal_sum,
    LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact hA.isSymmetric.coe_re_inner_self_apply (B j)

lemma trace_power_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (hA : IsSelfAdjoint A) (r : ℕ) :
    (((LinearMap.trace ℂ V (A^r).toLinearMap).re : ℝ):ℂ) =
      LinearMap.trace ℂ V (A^r).toLinearMap := trace_real _ (hA.pow r)

lemma traceMoment_real (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (r : ℕ) :
    (traceMoment d μ e r:ℂ) =
      LinearMap.trace ℂ (Specht.hilbertSpace μ) ((K d μ e)^r).toLinearMap := by
  exact trace_power_real (V:=Specht.hilbertSpace μ) _ (K_selfadjoint d μ e) r

theorem casimir_main : MainStatement := by
  obtain ⟨a,ha,hnorm⟩ := level_contraction
  refine ⟨a,1+64*(1+heightDecay 1),ha,by linarith [heightDecay_nonneg 1],?_,?_,?_⟩
  · intro d k _ hk x
    exact density_bound d k hk x
  · intro d μ e hk
    exact ⟨hnorm d μ e hk,trace_bound d μ e⟩
  · obtain ⟨l,hl,hm⟩ := physical_convergence
    refine ⟨l,hl,fun starts => ?_⟩
    simpa only [fromDistance_eq] using hm

end Thorp.Casimir

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht UnitaryFinite

def MainStatement : Prop :=
  ∃ p Cdensity C : ℝ, 1 < p ∧ p ≤ 2 ∧ DensityAt p Cdensity ∧
    ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool),
      ‖SparseContact.sweepOperator d μ e rev‖^2 ≤
       Real.exp (C*(μ.card-μ.rowLen 0 : ℕ)) *
       (Module.finrank ℂ (Specht.space (tailDiagram μ)):ℝ)^(-((p-1)/p))

lemma dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space μ) ≤ μ.card.factorial := by
  have hdim : Module.finrank ℂ (space μ) ≤ Fintype.card (Tabloid μ) := by
    simpa using Submodule.finrank_le (space μ)
  have hrow : 1 ≤ Fintype.card (rowGroup μ) := Fintype.card_pos
  have hc := card_tabloid_mul_row μ
  nlinarith

lemma tail_card_exact (μ : YoungDiagram) :
    (tailDiagram μ).card = μ.card - μ.rowLen 0 := by
  rw [←card_cell,Fintype.card_congr (tailCellEquiv μ),tail_card]

lemma tail_dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space (tailDiagram μ)) ≤ (μ.card - μ.rowLen 0).factorial := by
  simpa only [tail_card_exact] using dimension_le_factorial (tailDiagram μ)

lemma sweep_sq_palindrome (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 =
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ := by
  rw [SparseContact.sweep_forward_norm, sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e)]
  change ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))‖^2 = _
  rw [show (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint =
    star (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))) from rfl]
  simpa only [pow_two] using (CStarRing.norm_self_mul_star (x := sampleOperator (V := hilbertSpace μ)
    (relabelledUnitary μ e) (fun ω => butterflyPerm d (decodeButterfly d ω)))).symm

lemma sweep_sq_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ 1 := by
  have h := SparseContact.sweep_norm_le_one d μ e rev
  nlinarith [norm_nonneg (SparseContact.sweepOperator d μ e rev)]

theorem strong_tail : MainStatement := by
  obtain ⟨a,h,ha,hh,dE⟩ := Specht.spectral_regimes
  obtain ⟨D0,hD0⟩ := Filter.eventually_atTop.mp dE
  let d0 := max D0 1
  let t : ℝ := min a (1/1000)
  have ht : 0 < t := lt_min ha (by norm_num)
  have hta : t ≤ a := min_le_left _ _
  have htq : t ≤ 1/1000 := min_le_right _ _
  let b := t/(1+t)
  have hden : 0 < 1+t := by linarith
  have hb : 0 < b := div_pos ht hden
  have hbt : b ≤ t := (div_le_iff₀ hden).mpr (by nlinarith [sq_nonneg t])
  have hba : b ≤ a := hbt.trans hta
  have hb1 : b ≤ 1 := (div_le_one hden).mpr (by linarith)
  let C := Real.log (((2^d0).factorial:ℕ):ℝ)
  have hC : 0 ≤ C := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d0))
  refine ⟨1+t,3+heightDecay 1,C,by linarith,by linarith,
    density_at_small_exponent (by linarith) (by linarith),?_⟩
  intro d μ e rev
  let k := μ.card - μ.rowLen 0
  let D : ℝ := Module.finrank ℂ (space (tailDiagram μ))
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast dimension_pos (tailDiagram μ)
  have hDp : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hμ : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  have hform : -(((1+t)-1)/(1+t)) = -b := by dsimp [b]; congr 1; ring
  rw [hform]
  change ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ Real.exp (C*k)*D^(-b)
  rw [Real.rpow_def_of_pos hDp,←Real.exp_add]
  by_cases hk : k=0
  · have hDone : D=1 := by
      have hn := tail_dimension_le_factorial μ
      change Module.finrank ℂ (space (tailDiagram μ)) ≤ k.factorial at hn
      rw [hk,Nat.factorial_zero] at hn
      have hu : D ≤ 1 := by dsimp [D]; exact_mod_cast hn
      linarith
    rw [hk,Nat.cast_zero,mul_zero,hDone,Real.log_one,zero_mul,add_zero,Real.exp_zero]
    exact sweep_sq_le_one d μ e rev
  · have hkpos : 0<k := by omega
    by_cases hd : d0 ≤ d
    · have hdpos : 0<d := by have := le_max_right D0 1; omega
      by_cases htall : (μ.card:ℝ)/2 < μ.colLen 0
      · rw [sweep_sq_palindrome,Specht.palindrome_tall_zero_general d hdpos μ e htall,
          @norm_zero (hilbertSpace μ →L[ℂ] hilbertSpace μ) _]
        exact (Real.exp_pos _).le
      · have hg := (hD0 d ((le_max_left _ _).trans hd) μ e hkpos (le_of_not_gt htall)).1
        have hrootpos : (0:ℝ)<Module.finrank ℂ (space μ) := by exact_mod_cast dimension_pos μ
        have hlogle : Real.log D ≤ Real.log (Module.finrank ℂ (space μ):ℝ) :=
          Real.log_le_log hDp (by dsimp [D]; exact_mod_cast tail_dimension_le μ)
        rw [sweep_sq_palindrome]
        apply hg.trans
        apply Real.exp_le_exp.mpr
        have hbound := mul_le_mul hba hlogle hlog ha.le
        have hck : 0 ≤ C*(k:ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
        nlinarith
    · have hpow : 2^d ≤ 2^d0 := Nat.pow_le_pow_right (by decide) (by omega)
      have hklarge : k ≤ 2^d0 := (by simp [k,hμ] : k ≤ 2^d).trans hpow
      have hdim : D ≤ ((2^d0).factorial:ℝ) := by
        dsimp [D]
        exact_mod_cast (tail_dimension_le_factorial μ).trans (Nat.factorial_le hklarge)
      have hlC : Real.log D ≤ C := Real.log_le_log hDp hdim
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hprod : b*Real.log D ≤ C*(k:ℝ) := by nlinarith
      apply (sweep_sq_le_one d μ e rev).trans
      exact Real.one_le_exp_iff.mpr (by nlinarith)

end Thorp.StrongTail


namespace Thorp.HarmonicBounds
open scoped BigOperators Classical
open Filter Casimir StrongSmoothing

lemma dimension_contraction :
    ∃ b : ℝ, 0<b ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
      W d μ e ≤ Real.exp (-b*Real.log (Module.finrank ℂ (Specht.space μ):ℝ)) := by
  obtain ⟨a,h,ha,hh,he⟩ := Specht.spectral_regimes
  obtain ⟨D,hD⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop 1))
  let B (d : ℕ) : ℝ := 1+Real.log ((2^d).factorial:ℝ)
  have hB (d : ℕ) : 0<B d := by
    have hh : 0≤Real.log ((2^d).factorial:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d))
    dsimp [B]; linarith
  let f (d : ℕ) : ℝ := -Real.log (blockGap d)/B d
  have hf (d : ℕ) : 0<f d :=
    div_pos (neg_pos.mpr (Real.log_neg (blockGap_pos d) (blockGap_lt_one d))) (hB d)
  obtain ⟨b,hb,hbD⟩ := finite_positive_lower f D (fun d _ => hf d)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro d μ e hk
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hDpos : (0:ℝ)<Module.finrank ℂ (Specht.space μ) := by exact_mod_cast Specht.dimension_pos μ
  have hL : 0≤Real.log (Module.finrank ℂ (Specht.space μ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast Specht.dimension_pos μ)
  by_cases hd : D≤d
  · obtain ⟨hs,hd1⟩ := hD d hd
    by_cases ht : (μ.card:ℝ)/2<μ.colLen 0
    · have hz := Specht.palindrome_tall_zero_general d (by omega) μ e ht
      change K d μ e=0 at hz
      change ‖K d μ e‖≤_
      rw [hz,@norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _]
      exact (Real.exp_pos _).le
    · apply (hs μ e hk (le_of_not_gt ht)).1.trans
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hL
      linarith
  · have hdim : Real.log (Module.finrank ℂ (Specht.space μ):ℝ) ≤ B d := by
      have hh := StrongTail.dimension_le_factorial μ
      rw [hμ] at hh
      have hl := Real.log_le_log hDpos (show (Module.finrank ℂ (Specht.space μ):ℝ)≤(2^d).factorial by exact_mod_cast hh)
      dsimp [B]; linarith
    have hab : min a b≤f d := (min_le_right _ _).trans (hbD d (by omega))
    have hp := mul_le_mul_of_nonneg_right hab (hB d).le
    have heq : f d*B d = -Real.log (blockGap d) := by dsimp [f]; field_simp [ne_of_gt (hB d)]
    rw [heq] at hp
    have hscale := mul_le_mul_of_nonneg_left hdim (le_of_lt (lt_min ha hb))
    calc
      W d μ e ≤ blockGap d := nontrivial_gap d μ e hk
      _ = Real.exp (Real.log (blockGap d)) := (Real.exp_log (blockGap_pos d)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma exp_intersection {x A B : ℝ} (hx : 0≤x) (hA : x≤Real.exp A) (hB : x≤Real.exp B) :
    x≤Real.exp ((A+B)/2) := by
  have hh := mul_le_mul hA hB hx (Real.exp_pos A).le
  rw [←Real.exp_add] at hh
  have he : Real.exp ((A+B)/2)^2=Real.exp (A+B) := by
    rw [pow_two,←Real.exp_add]
    congr 1; ring
  nlinarith [Real.exp_pos ((A+B)/2)]

lemma flat_tuple_trace (d k : ℕ) (hk : k≤2^d) (order : Equiv.Perm (Fin d)) (rev : Bool) :
    tupleTrace d k order rev 2001 ≤ Real.exp ((2000*(1+heightDecay 1))*k) := by
  have hpos : 0<Fintype.card (Tuples d k) := by
    rw [tuples_card]
    exact Nat.descFactorial_pos.mpr hk
  have hne : (Fintype.card (Tuples d k):ℝ)≠0 := by exact_mod_cast ne_of_gt hpos
  calc
    _ ≤ ∑ x : Tuples d k, Real.exp ((2000*(1+heightDecay 1))*k)/
        ((2^d).descFactorial k:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact both_pointwise d k order rev x x
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←tuples_card]
      field_simp

theorem harmonic_cycle_main : MainStatement := by
  obtain ⟨a,ha,hlevel⟩ := level_contraction
  obtain ⟨b,hb,hdim⟩ := dimension_contraction
  let C : ℝ := 2000*(1+heightDecay 1)
  have hA : 0≤heightDecay 1 := heightDecay_nonneg 1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨a,C,b,1/1000,min a b/4,a/2,b/2,2001,
    ha,hC,hb,by norm_num,by norm_num,by positivity,by positivity,by positivity,by norm_num,?_,?_⟩
  · intro d μ e hk
    dsimp only
    let L := levelScale (2^d) (μ.card-μ.rowLen 0)
    let f : ℝ := Module.finrank ℂ (Specht.space (tail μ))
    let D : ℝ := Module.finrank ℂ (Specht.space μ)
    have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
    have hkn : μ.card-μ.rowLen 0≤2^d := by omega
    have hL : 0≤L := (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
    have hfp : 0<f := by dsimp [f,tail]; exact_mod_cast Specht.dimension_pos (StrongTail.tailDiagram μ)
    have hfl : 0≤Real.log f := Real.log_nonneg (by dsimp [f,tail]; exact_mod_cast Specht.dimension_pos (StrongTail.tailDiagram μ))
    have hDp : 0<D := by dsimp [D]; exact_mod_cast Specht.dimension_pos μ
    have hle : Real.log f≤Real.log D := Real.log_le_log hfp (by
      dsimp [f,D,tail]; exact_mod_cast StrongTail.tail_dimension_le μ)
    have hw := hlevel d μ e hk
    have hd := hdim d μ e hk
    change W d μ e≤Real.exp (-a*L) at hw
    change W d μ e≤Real.exp (-b*Real.log D) at hd
    have ht : W d μ e≤Real.exp (-b*Real.log f) := hd.trans (Real.exp_le_exp.mpr (by nlinarith))
    refine ⟨hw,?_,?_,?_⟩
    · change W d μ e≤Real.exp (C*L)*f^(-b)
      rw [Real.rpow_def_of_pos hfp,←Real.exp_add]
      exact ht.trans (Real.exp_le_exp.mpr (by nlinarith))
    · intro rev
      have hg := exp_intersection (norm_nonneg (K d μ e)) hw ht
      have hcoef : (-a*L+-b*Real.log f)/2 ≤ -2*(min a b/4)*(L+Real.log f) := by
        have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) hL
        have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) hfl
        nlinarith
      have hg' := hg.trans (Real.exp_le_exp.mpr hcoef)
      have hs := StrongTail.sweep_sq_palindrome d μ e rev
      change ‖SparseContact.sweepOperator d μ e rev‖^2=W d μ e at hs
      change W d μ e≤_ at hg'
      rw [←hs] at hg'
      have he : Real.exp (-(min a b/4)*(L+Real.log f))^2 =
          Real.exp (-2*(min a b/4)*(L+Real.log f)) := by
        rw [pow_two,←Real.exp_add]
        congr 1; ring
      change ‖SparseContact.sweepOperator d μ e rev‖≤Real.exp (-(min a b/4)*(L+Real.log f))
      nlinarith [Real.exp_pos (-(min a b/4)*(L+Real.log f))]
    · change W d μ e≤Real.exp (-(a/2)*L)*D^(-(b/2))
      rw [Real.rpow_def_of_pos hDp,←Real.exp_add]
      have hg := exp_intersection (norm_nonneg (K d μ e)) hw hd
      have he : -(a/2)*L+Real.log D*(-(b/2))=(-a*L+-b*Real.log D)/2 := by ring
      rw [he]
      exact hg
  · intro d k _ hk order rev
    have hL := levelScale_ge (2^d) k hk
    have hcoef : k*(1+heightDecay 1) ≤ C*levelScale (2^d) k := by
      have hk0 : (0:ℝ)≤k := by positivity
      dsimp [C]; nlinarith
    refine ⟨?_,?_⟩
    · intro x
      exact (StrongTail.reflected_moment_both d k order rev x).trans (Real.exp_le_exp.mpr hcoef)
    · exact (flat_tuple_trace d k hk order rev).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hC.le))

end Thorp.HarmonicBounds

end ThorpNine.Harmonic

end OAI
