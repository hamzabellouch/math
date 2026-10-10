import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceAllocatedProfile
import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open CenteredMomentOriginalReflectionErrorMass
local notation "O" => HeckeFamily.O

theorem naturalSlot_ideal_bound (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P : ℝ) (hM : 0≤M) (hP : 0<P)
    (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool β P‖≤(128*max 1 b*M)*Real.sqrt P := by
  let f : Ideal O→ℂ:=fun I=>if I∈pool then idealCoeff χ I*β I else 0
  have hf0 : f 0=0:=by simp only [f,idealCoeff_zero,zero_mul,ite_self]
  have hf : ∀I,‖f I‖≤M := by
    intro I
    by_cases hi : I∈pool
    · simp only [f,ite_eq_left hi,norm_mul]
      exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hβ I hi) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    · simpa only [f,ite_eq_right hi,norm_zero] using hM
  have hsup : ∀I,f I≠0 → (I.absNorm:ℝ)≤max 1 b*P := by
    intro I hi
    have hm : I∈pool:=by by_contra hn;exact hi (by simp only [f,ite_eq_right hn])
    have hb : β I≠0:=by intro hz;exact hi (by simp only [f,ite_eq_left hm,hz,mul_zero])
    exact (hs I hm hb).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hP.le)
  have he : (∑'I:Ideal O,f I)=∑I∈pool,idealCoeff χ I*β I := by
    rw [tsum_eq_sum (s:=pool) (fun I hi=>by simp only [f,ite_eq_right hi])]
    exact Finset.sum_congr rfl (fun I hi=>by simp only [f,ite_eq_left hi])
  have hh:=norm_tsum_ideal_ball f (max 1 b*P) M (by positivity) hM hf0 hf hsup
  rw [he] at hh
  unfold naturalSlot
  rw [←inverse_half_power P hP.le]
  apply normalized_linear_bound P _ hP
  convert hh using 1 ; ring

theorem naturalSlot_height_bound (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P t : ℝ) (hM : 0≤M) (hP : 0<P)
    (hp : ∀I∈pool,Prime I) (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool (heightCoefficient β t) P‖≤(128*max 1 b*M)*Real.sqrt P := by
  apply naturalSlot_ideal_bound χ pool _ b M P hM hP
  · intro I hi
    rw [heightCoefficient_norm _ _ _ (hp I hi).ne_zero]
    exact hβ I hi
  · intro I hi hn
    exact hs I hi (left_ne_zero_of_mul hn)

theorem natural_remaining_sq_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort Bshort b M*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort Bshort b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort*Bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ errorConstant F bshort Bshort b M*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

lemma allocated_profile_supnorm :
    ∃n : ℕ,∃A : ℝ,0<A ∧ ∀reverse : Bool,∀k : ℕ,k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t h U : ℝ,∀hU : 0<U,∀x : ℝ,
      ‖(detectorPlain reverse k σ t).profile U hU h x‖≤A*(1+‖t‖+‖h‖)^n := by
  obtain ⟨n,A,hA,hb⟩:=detectorPlain_profile_uniform {(0,0)}
  refine ⟨n,A,hA,?_⟩
  intro reverse k hk σ hσ t h U hU x
  apply (SchwartzMap.norm_le_seminorm ℝ ((detectorPlain reverse k σ t).profile U hU h) x).trans
  simpa using hb reverse k hk σ hσ t h U hU

lemma errorConstant_height {α : Type*} (F : Finset α) (bshort A : ℝ) (b M : α→ℝ)
    (w : ℝ) (hw : 1≤w) :
    errorConstant F bshort (A*w) b M≤errorConstant F bshort A b M*w^2 := by
  unfold errorConstant
  have hh : 1+(128*max 1 bshort*(A*w))^2≤(1+(128*max 1 bshort*A)^2)*w^2 := by
    nlinarith [sq_nonneg (w-1)]
  calc
    _≤((1+(128*max 1 bshort*A)^2)*w^2)*∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      mul_le_mul_of_nonneg_right hh (Finset.prod_nonneg (fun _ _=>by positivity))
    _=_ := by ring

theorem allocated_natural_error_point {α : Type*} (F : Finset α) (b M : α→ℝ)
    (hM : ∀j∈F,0≤M j) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀T : Finset α,T⊆F →
      ∀reverse : Bool,∀k : ℕ,k≤2 → ∀σ∈Set.Icc (0:ℝ) 1,
      ∀t h U : ℝ,∀hU : 0<U,∀χ : Character,
      ∀pool : α→Finset (Ideal O),∀β : α→Ideal O→ℂ,∀P freq : α→ℝ,
      ∀X omega : ℝ,0<X → (∀j∈T,0<P j) →
      (∀j∈T,∀I∈pool j,Prime I) → (∀j∈T,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      ‖polynomial χ false ((detectorPlain reverse k σ t).profile U hU h) X 0 omega*
        ∏j∈T,naturalSlot χ (pool j) (heightCoefficient (β j) (freq j)) (P j)‖^2≤
      C*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) := by
  obtain ⟨n,A,hA,hprofile⟩:=allocated_profile_supnorm
  refine ⟨n,errorConstant F (9/4) A b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT reverse k hk σ hσ t h U hU χ pool β P freq X omega hX hP hp hβ hs
  let w : ℝ:=(1+‖t‖+‖h‖)^n
  have hw : 1≤w:=one_le_pow₀ (by linarith [norm_nonneg t,norm_nonneg h] : (1:ℝ)≤1+‖t‖+‖h‖)
  have hh:=natural_remaining_sq_bound F T hT ((detectorPlain reverse k σ t).profile U hU h)
    (9/4) (A*w) b M (by positivity) hM (hprofile reverse k hk σ hσ t h U hU)
    (fun x hx=>(detectorPlain_profile_support reverse k σ t U hU h hx).2)
    χ pool (fun j=>heightCoefficient (β j) (freq j)) P X omega hX hP
    (by intro j hj I hi;rw [heightCoefficient_norm _ _ _ (hp j hj I hi).ne_zero];exact hβ j hj I hi)
    (by intro j hj I hi hn;exact hs j hj I hi (left_ne_zero_of_mul hn))
  apply hh.trans
  have hc:=mul_le_mul_of_nonneg_right (errorConstant_height F (9/4) A b M w hw)
    (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
  have hw2 : w^2=(1+‖t‖+‖h‖)^(2*n) := by
    dsimp only [w]
    rw [←pow_mul,Nat.mul_comm n 2]
  rw [hw2] at hc
  convert hc using 1 <;> ring

theorem allocated_natural_radial_error_mass {α : Type*} (F : Finset α) (b M : α→ℝ)
    (hM : ∀j∈F,0≤M j) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀T : Finset α,T⊆F →
      ∀reverse : Bool,∀k : ℕ,k≤2 → ∀σ∈Set.Icc (0:ℝ) 1,
      ∀t h U : ℝ,∀hU : 0<U,∀χ : O→Character,
      ∀pool : O→α→Finset (Ideal O),∀β : O→α→Ideal O→ℂ,∀freq : O→α→ℝ,
      ∀P : α→ℝ,∀omega : O→ℝ,∀X K : ℝ,∀Φ : 𝓢(ℝ,ℂ),
      0<X → (∀j∈T,0<P j) → 0<K →
      (∀z j,j∈T → ∀I∈pool z j,Prime I) →
      (∀z j,j∈T → ∀I∈pool z j,‖β z j I‖≤M j) →
      (∀z j,j∈T → ∀I∈pool z j,β z j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      let R:=fun z:O=>polynomial (χ z) false ((detectorPlain reverse k σ t).profile U hU h) X 0 (omega z)*
        ∏j∈T,naturalSlot (χ z) (pool z j) (heightCoefficient (β z j) (freq z j)) (P j)
      Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2) ∧
      (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
        C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) ∧
      ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
        C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n) := by
  obtain ⟨n,C,hC,hpoint⟩:=allocated_natural_error_point F b M hM
  refine ⟨n,C,hC,?_⟩
  intro T hT reverse k hk σ hσ t h U hU χ pool β freq P omega X K Φ hX hP hK hp hβ hs R
  let A:=C*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n)
  have hA : 0≤A:=by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC.le hX.le) (Finset.prod_nonneg (fun j hj=>(hP j hj).le))) (by positivity)
  have hr (z:O):‖R z‖^2≤A:=hpoint T hT reverse k hk σ hσ t h U hU (χ z)
    (pool z) (β z) P (freq z) X (omega z) hX hP (hp z) (hβ z) (hs z)
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right A)
  have hb:(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)≤
      C*diagonalControl Φ*max 1 K*X*(∏j∈T,P j)*(1+‖t‖+‖h‖)^(2*n):=by
    calc
      _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*A:=hsum.tsum_le_tsum
        (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
        ((radial_norm_summable Φ K hK).mul_right A)
      _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*A:=tsum_mul_right
      _≤(diagonalControl Φ*max 1 K)*A:=
        mul_le_mul_of_nonneg_right (radial_weight_lattice_bound_all Φ K hK) hA
      _=_:=by dsimp [A];ring
  refine ⟨hsum,hb,?_⟩
  intro E
  exact (sum_le_hasSum E (fun z _=>mul_nonneg (norm_nonneg _) (sq_nonneg _)) hsum.hasSum).trans hb

theorem radialEnergy_le_absolute_mass (R : O→ℂ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hPhi : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (hs : Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2)) :
    CenteredMomentOriginalRadialComparison.radialEnergy R keep Φ K≤
      ∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
  let f:=fun z:O=>if keep z then ‖R z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hn (z:O):0≤f z:=by dsimp only [f];split_ifs;exact mul_nonneg (sq_nonneg _) (hPhi z);exact le_rfl
  have hb (z:O):f z≤‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2 := by
    dsimp only [f]
    split_ifs
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Complex.re_le_norm (Φ (‖eisEmbedding z‖^2/K))) (sq_nonneg ‖R z‖)
    · positivity
  exact (Summable.of_nonneg_of_le hn hb hs).tsum_le_tsum hb hs

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
