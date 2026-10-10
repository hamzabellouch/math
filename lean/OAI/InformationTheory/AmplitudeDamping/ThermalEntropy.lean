import OAI.InformationTheory.AmplitudeDamping.ZeroBlockEntropy

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def thermal (X Y : Matrix ι κ ℂ) (a b c d K : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (a • gram X+b • gram Y) (K • (X*Yᴴ))
    (K • (Y*Xᴴ)) (c • gram X+d • gram Y)

omit [DecidableEq κ] in
theorem isState_of_posSemidef_trace_re {P : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (ht : P.trace.re = 1) : IsState P := by
  refine ⟨hP, ?_⟩
  apply Complex.ext ht
  exact (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm

omit [DecidableEq ι] [DecidableEq κ] in
theorem thermal_trace (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    (a b c d K : ℝ) : (thermal X Y a b c d K).trace.re = a+b+c+d := by
  simp only [mass, Matrix.trace, Matrix.diag, Complex.re_sum] at hX hY
  simp [thermal, Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Finset.sum_add_distrib,
    ← Finset.mul_sum, hX, hY, add_assoc]

def blockSwap : Matrix.unitaryGroup (ι ⊕ ι) ℂ :=
  ⟨Matrix.fromBlocks 0 1 1 0, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]⟩

omit [DecidableEq κ] in
theorem blockSwap_conj (A B C D : Matrix ι ι ℂ) :
    Unitary.conjStarAlgAut ℂ _ (blockSwap (ι := ι)) (Matrix.fromBlocks A B C D) =
    Matrix.fromBlocks D C B A := by
  simp [Unitary.conjStarAlgAut_apply, blockSwap, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_zeroEta_gram (X Y : Matrix ι κ ℂ) {a b d K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : 0 ≤ K) (had : a*d = K^2) :
    thermal X Y a b 0 d K =
      gram (zeroBlock (Real.sqrt a • X) (Real.sqrt b • Y) (Real.sqrt d • Y)) := by
  have hroot : Real.sqrt a * Real.sqrt d = K := by
    rw [← Real.sqrt_mul ha, had, Real.sqrt_sq hK]
  rw [gram_zeroBlock, gram_sqrt_smul ha, gram_sqrt_smul hb, gram_sqrt_smul hd]
  simp only [thermal, zero_smul, zero_add, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hroot, mul_comm (Real.sqrt d) (Real.sqrt a)]

theorem thermal_zeroEta (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a b d K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hs : a+b+d=1) (had : a*d=K^2) :
    IsState (thermal X Y a b 0 d K) ∧
      a*entropy (gram X)+(b+d)*entropy (gram Y)+g (b*d) ≤ entropy (thermal X Y a b 0 d K) := by
  have hp : (thermal X Y a b 0 d K).PosSemidef := by
    rw [thermal_zeroEta_gram X Y ha hb hd hK had]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  refine ⟨isState_of_posSemidef_trace_re hp ?_, ?_⟩
  · rw [thermal_trace X Y hX hY]; linarith
  · rw [thermal_zeroEta_gram X Y ha hb hd hK had]
    have h := zeroBlock_normalized X Y Y hX hY hY ha hb hd hs
    linarith

theorem thermal_zeroBeta (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a c d K : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hs : a+c+d=1) (had : a*d=K^2) :
    IsState (thermal X Y a 0 c d K) ∧
      (a+c)*entropy (gram X)+d*entropy (gram Y)+g (c*a) ≤ entropy (thermal X Y a 0 c d K) := by
  have hh := thermal_zeroEta Y X hY hX hd hc ha hK (by linarith) (by nlinarith [had])
  have he : thermal X Y a 0 c d K = Unitary.conjStarAlgAut ℂ _ (blockSwap (ι := ι))
      (thermal Y X d c 0 a K) := by
    simp only [thermal, blockSwap_conj]
    simp [add_comm]
  have hen : entropy (thermal X Y a 0 c d K) = entropy (thermal Y X d c 0 a K) := by
    rw [he, entropy_unitary_conj _ hh.1.1.isHermitian]
  refine ⟨?_, ?_⟩
  · have hp : (thermal X Y a 0 c d K).PosSemidef := by
      rw [he, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      exact hh.1.1.mul_mul_conjTranspose_same _
    exact isState_of_posSemidef_trace_re hp (by rw [thermal_trace X Y hX hY]; linarith)
  · rw [hen]
    nlinarith [hh.2]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_mix (X Y : Matrix ι κ ℂ) (a b c d a' b' c' d' K w w' : ℝ)
    (hw : w+w'=1) :
    w • thermal X Y a b c d K + w' • thermal X Y a' b' c' d' K =
      thermal X Y (w*a+w'*a') (w*b+w'*b') (w*c+w'*c') (w*d+w'*d') K := by
  have hK : w*K+w'*K=K := by rw [← add_mul, hw, one_mul]
  simp only [thermal, Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_add, smul_smul,
    ]
  congr 1
  · module
  · rw [← add_smul, hK]
  · rw [← add_smul, hK]
  · module

/-- The exact finite-dimensional thermal inequality, including all coefficient boundaries. -/
theorem thermal_entropy (X Y : Matrix ι κ ℂ) (hX : mass X = 1) (hY : mass Y = 1)
    {a b c d K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hK : 0 ≤ K) (hs : a+b+c+d=1) (hk : a*d-b*c=K^2) :
    let u := (a+b)*(c+d)-K^2
    IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u ≤ entropy (thermal X Y a b c d K) := by
  dsimp only
  let U := a+b
  let V := c+d
  let u := U*V-K^2
  have hU : 0 ≤ U := add_nonneg ha hb
  have hV : 0 ≤ V := add_nonneg hc hd
  have hUV : U+V=1 := by dsimp [U,V]; linarith
  have hu : u=b*V+c*U := by dsimp [u,U,V]; nlinarith only [hk]
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have huUV : u ≤ U*V := by dsimp [u]; nlinarith only [sq_nonneg K]
  have huq : u ≤ 1/4 := by nlinarith only [sq_nonneg (U-V), hUV, huUV]
  change IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧ _
  have hgoal (hstate : IsState (thermal X Y a b c d K))
      (hbound : (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u ≤ entropy (thermal X Y a b c d K)) :
      IsState (thermal X Y a b c d K) ∧ u ∈ Set.Icc (0 : ℝ) (1/4) ∧
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g ((a+b)*(c+d)-K^2) ≤ entropy (thermal X Y a b c d K) :=
    ⟨hstate, ⟨hu0,huq⟩, hbound⟩
  by_cases hb0 : b=0
  · subst b
    have ht := thermal_zeroBeta X Y hX hY ha hc hd hK (by linarith) (by nlinarith only [hk])
    apply hgoal ht.1
    have hue : u=c*a := by dsimp [u,U,V]; nlinarith only [hk]
    simpa only [hue, zero_add] using ht.2
  by_cases hc0 : c=0
  · subst c
    have ht := thermal_zeroEta X Y hX hY ha hb hd hK (by linarith) (by nlinarith only [hk])
    apply hgoal ht.1
    have hue : u=b*d := by dsimp [u,U,V]; nlinarith only [hk]
    simpa only [hue, add_zero] using ht.2
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hUp : 0 < U := by dsimp [U]; linarith
  have hVp : 0 < V := by dsimp [V]; linarith
  have hup : 0 < u := by rw [hu]; positivity
  let w := b*V/u
  let w' := c*U/u
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw' : 0 ≤ w' := by dsimp [w']; positivity
  have hww : w+w'=1 := by dsimp [w,w']; rw [← add_div, ← hu, div_self hup.ne']
  have hrow1 : K^2/V+u/V = U := by rw [← add_div]; apply (div_eq_iff hVp.ne').mpr; dsimp [u]; ring
  have hrow2 : u/U+K^2/U = V := by rw [← add_div]; apply (div_eq_iff hUp.ne').mpr; dsimp [u]; ring
  have hprod1 : (K^2/V)*V=K^2 := div_mul_cancel₀ _ hVp.ne'
  have hprod2 : U*(K^2/U)=K^2 := mul_div_cancel₀ _ hUp.ne'
  have hg1 : (u/V)*V=u := div_mul_cancel₀ _ hVp.ne'
  have hg2 : (u/U)*U=u := div_mul_cancel₀ _ hUp.ne'
  have hwb : w*(u/V)=b := by dsimp [w]; field_simp
  have hwc : w'*(u/U)=c := by dsimp [w']; field_simp
  have hwa : w*(K^2/V)+w'*U=a := by
    have hh := congrArg (fun r : ℝ ↦ w*r) hrow1
    have hh' := congrArg (fun r : ℝ ↦ r*U) hww
    dsimp only [U] at hh hh' ⊢
    linear_combination hh + hh' - hwb
  have hwd : w*V+w'*(K^2/U)=d := by
    have hh := congrArg (fun r : ℝ ↦ w'*r) hrow2
    have hh' := congrArg (fun r : ℝ ↦ r*V) hww
    dsimp only [V] at hh hh' ⊢
    linear_combination hh + hh' - hwc
  have h1 := thermal_zeroEta X Y hX hY (div_nonneg (sq_nonneg K) hV)
    (div_nonneg hu0 hV) hV hK (by linarith [hrow1]) hprod1
  have h2 := thermal_zeroBeta X Y hX hY hU (div_nonneg hu0 hU)
    (div_nonneg (sq_nonneg K) hU) hK (by linarith [hrow2]) hprod2
  let T1 := thermal X Y (K^2/V) (u/V) 0 V K
  let T2 := thermal X Y U 0 (u/U) (K^2/U) K
  have hmix : w • T1+w' • T2=thermal X Y a b c d K := by
    rw [thermal_mix X Y _ _ _ _ _ _ _ _ _ _ _ hww]
    simp only [hwa, hwd, mul_zero, add_zero, zero_add, hwb, hwc]
  have hpos : (thermal X Y a b c d K).PosSemidef := by
    rw [← hmix]
    exact (h1.1.1.smul hw).add (h2.1.1.smul hw')
  apply hgoal (isState_of_posSemidef_trace_re hpos (by rw [thermal_trace X Y hX hY]; exact hs))
  have hconc := (concaveOn_entropy (ι := ι ⊕ ι)).2 h1.1.1 h2.1.1 hw hw' hww
  change w*entropy T1+w'*entropy T2 ≤ entropy (w • T1+w' • T2) at hconc
  rw [hmix] at hconc
  have hh1 := mul_le_mul_of_nonneg_left h1.2 hw
  have hh2 := mul_le_mul_of_nonneg_left h2.2 hw'
  rw [hg1] at hh1
  rw [hg2] at hh2
  have hcoeffX : w*(K^2/V)+w'*(U+u/U)=a+c := by linear_combination hwa + hwc
  have hcoeffY : w*(u/V+V)+w'*(K^2/U)=b+d := by linear_combination hwd + hwb
  have heq : w*((K^2/V)*entropy (gram X)+(u/V+V)*entropy (gram Y)+g u)+
      w'*((U+u/U)*entropy (gram X)+(K^2/U)*entropy (gram Y)+g u) =
      (a+c)*entropy (gram X)+(b+d)*entropy (gram Y)+g u := by
    calc
      _ = (w*(K^2/V)+w'*(U+u/U))*entropy (gram X)+
        (w*(u/V+V)+w'*(K^2/U))*entropy (gram Y)+(w+w')*g u := by ring
      _ = _ := by rw [hcoeffX,hcoeffY,hww,one_mul]
  dsimp only [T1,T2] at hconc
  linarith only [hh1, hh2, hconc, heq]

end GAD

end

end OAI
