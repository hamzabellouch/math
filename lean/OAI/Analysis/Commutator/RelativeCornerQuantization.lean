import Mathlib
import OAI.Analysis.Commutator.CornerPolarTransfer
import OAI.Analysis.Commutator.LocalQuantization
import OAI.Analysis.Commutator.PolarSupport
import OAI.Analysis.Commutator.TracialConjugation
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.RelativeCornerQuantization

open TracialL2 CornerPolarTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ in
theorem exists_polar_cut (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    {c t : ℝ} (hc : 0 ≤ c) (hct : c*c*t=1) :
    ∃ f : M, IsStarProjection f ∧ f ≤ p ∧ (τ f).re ≤ (τ q).re ∧
      (τ q).re-(τ f).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 ∧
      (∀ y : M, p*y=y → y*p=y → norm τ (f*y*f) ≤ 
        c^2*norm τ (q*y*q)+(1+c)*‖y‖*c^2*norm τ (q*(p-t • (1:M))*q)) ∧
      (∀ N : VonNeumannAlgebra H, (p : H →L[ℂ] H)∈N → (q : H →L[ℂ] H)∈N →
        (f : H →L[ℂ] H)∈N) := by
  let b : M := c • (p*q)
  have hpb : p*b=b := by dsimp [b]; rw [mul_smul_comm,←mul_assoc,hp.isIdempotentElem.eq]
  have hbq : b*q=b := by dsimp [b]; rw [smul_mul_assoc,mul_assoc,hq.isIdempotentElem.eq]
  obtain ⟨v,hva,hr,hf,hra,hvn,hvN,hleft,hright⟩ := exists_polar_data M b
  have hrq : star v*v ≤ q := hright q hq hbq
  have haq : CFC.abs b*q=CFC.abs b := by
    apply Subtype.ext
    change ((CFC.abs b : M) : H →L[ℂ] H)*(q : H →L[ℂ] H)=((CFC.abs b : M) : H →L[ℂ] H)
    rw [←abs_coe M]
    exact Polar.abs_mul_of_mul _ _ (congrArg (fun a : M => (a : H →L[ℂ] H)) hbq)
  have hdef : norm τ (v-b) ≤ c^2*norm τ (q*(p-t • (1:M))*q) := by
    have h := defect_bound τ hq hr hrq (CFC.abs_nonneg b) hra haq rfl
    rw [hva,CFC.abs_mul_abs] at h
    exact h.trans_eq (norm_scaled_projection_defect τ hp hq hct)
  have hker : (τ q).re-(τ (star v*v)).re ≤ (c^2*norm τ (q*(p-t • (1:M))*q))^2 := by
    have h := trace_kernel_bound τ hq hr (CFC.abs_nonneg b) hra haq
    rw [CFC.abs_mul_abs,norm_scaled_projection_defect τ hp hq hct] at h
    exact h
  have htr : τ (star v*v)=τ (v*star v) := hτ _ _
  have hbn : ‖b‖ ≤ c := by
    dsimp [b]
    rw [_root_.norm_smul,Real.norm_of_nonneg hc]
    have hpqn : ‖p*q‖ ≤ 1 := (_root_.norm_mul_le _ _).trans
      ((mul_le_mul (hp.norm_le p) (hq.norm_le q) (_root_.norm_nonneg _) (by norm_num)).trans_eq
        (one_mul (1:ℝ)))
    exact mul_le_of_le_one_right hc hpqn
  refine ⟨v*star v,hf,hleft p hp hpb,?_,by simpa only [htr] using hker,?_,?_⟩
  · have h := (τ.monotone hrq).1
    change (τ (star v*v)).re ≤ (τ q).re at h
    simpa only [htr] using h
  · intro y hpy hyp
    calc
      _ ≤ c^2*norm τ (q*y*q)+(1+‖b‖)*‖y‖*norm τ (v-b) :=
        compressed_scalar_polar τ hτ hp hq hpy hyp rfl hvn
      _ ≤ c^2*norm τ (q*y*q)+(1+c)*‖y‖*(c^2*norm τ (q*(p-t • (1:M))*q)) := by
        apply add_le_add le_rfl
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (add_le_add le_rfl hbn) (_root_.norm_nonneg y))
          hdef (norm_nonneg τ _) (mul_nonneg (by positivity) (_root_.norm_nonneg y))
      _=_ := by rw [mul_assoc ((1+c)*‖y‖)]
  · intro N hpN hqN
    have hbN : (b : H →L[ℂ] H)∈N := by
      change ((c:ℂ) • ((p : H →L[ℂ] H)*(q : H →L[ℂ] H)))∈N
      exact N.toStarSubalgebra.smul_mem (N.mul_mem hpN hqN) _
    exact N.mul_mem (hvN N hbN) (N.star_mem' (hvN N hbN))

section Quantization

variable {J : Type*} [Fintype J]

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, LinearOrder (ι n)]
  [∀ n, Nonempty (ι n)]

variable (stage : ∀ n, Matrix (ι n) (ι n) ℂ →⋆ₐ[ℂ] M)

variable (hmono : ∀ {n m : ℕ}, n ≤ m → (stage n).range ≤ (stage m).range)

include hτ hmono in
theorem exists_relative_centered_compression
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ n (x : Matrix (ι n) (ι n) ℂ), stage n x*b=b*stage n x) →
      ∃ c : ℂ, b=algebraMap ℂ M c)
    (hgrow : Tendsto (fun n => (Fintype.card (ι n):ℝ)) atTop atTop)
    (N : VonNeumannAlgebra H)
    (hstage : ∀ n a, (stage n a : H →L[ℂ] H)∈N)
    (p : M) (hpN : (p : H →L[ℂ] H)∈N) (hp : IsStarProjection p)
    (hpt : 0<(τ p).re)
    (x : J → M) (hx : ∀ j, τ (x j)=0) (hpx : ∀ j,p*x j=x j) (hxp : ∀ j,x j*p=x j)
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ f : M, (f : H →L[ℂ] H)∈N ∧ IsStarProjection f ∧ f ≤ p ∧
      0<(τ f).re ∧ (τ f).re<η ∧ ∀ j, norm τ (f*x j*f)^2<ε^2*(τ f).re := by
  classical
  let t : ℝ := (τ p).re
  have ht : 0<t := hpt
  let c : ℝ := (Real.sqrt t)⁻¹
  have hc : 0<c := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hct : c*c*t=1 := by
    dsimp [c]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]
    nlinarith only [Real.sq_sqrt ht.le]
  let B : ℝ := ∑ j, ‖x j‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => _root_.norm_nonneg (x j))
  have hxB (j : J) : ‖x j‖ ≤ B :=
    Finset.single_le_sum (fun i _ => _root_.norm_nonneg (x i)) (Finset.mem_univ j)
  let K : ℝ := c^2+(1+c)*B*c^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ : ℝ := min (1/(2*(c^2+1))) (ε/(2*(K+1)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδc : c^2*δ ≤ 1/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*(c^2+1))).mp (min_le_left
      (1/(2*(c^2+1))) (ε/(2*(K+1))))
    change δ*(2*(c^2+1)) ≤ 1 at h
    nlinarith only [h,hδ]
  have hδK : K*δ ≤ ε/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*(K+1))).mp (min_le_right
      (1/(2*(c^2+1))) (ε/(2*(K+1))))
    change δ*(2*(K+1)) ≤ ε at h
    nlinarith only [h,hδ]
  let z : Option J → M := fun j => match j with
    | none => p-t • (1:M)
    | some j => x j
  have htrace : τ p=(t:ℂ) := Complex.ext rfl (τ.map_nonneg hp.nonneg).2.symm
  have hz : ∀ j,τ (z j)=0 := by
    intro j
    cases j with
    | none => simp [z,map_sub,PositiveLinearMap.map_smul_of_tower,hone,htrace]
    | some j => exact hx j
  obtain ⟨n,q,hqstage,hq,hqt,hqη,hsum⟩ :=
    LocalQuantization.exists_centered_compression M τ hτ stage hmono hnormal hfaith hone hirr
      hgrow z hz hδ hη
  have hqN : (q : H →L[ℂ] H)∈N := by
    obtain ⟨a,rfl⟩ := hqstage
    exact hstage n a
  have hsum' : (∑ j, norm τ (q*z j*q)^2)<δ^2*(τ q).re := by
    simpa only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe,TracialL2.norm] using hsum
  let s : ℝ := Real.sqrt (τ q).re
  have hs : 0<s := Real.sqrt_pos.mpr hqt
  have hs2 : s^2=(τ q).re := Real.sq_sqrt hqt.le
  have hsmall (j : Option J) : norm τ (q*z j*q) ≤ δ*s := by
    apply (sq_le_sq₀ (norm_nonneg τ _) (mul_nonneg hδ.le hs.le)).mp
    have hj : norm τ (q*z j*q)^2 ≤ ∑ i,norm τ (q*z i*q)^2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (norm τ (q*z i*q))) (Finset.mem_univ j)
    rw [mul_pow,hs2]
    exact hj.trans hsum'.le
  obtain ⟨f,hf,hfp,hfq,hker,hcomp,hN⟩ := exists_polar_cut M τ hτ p q hp hq hc.le hct
  have hd : c^2*norm τ (q*(p-t • (1:M))*q) ≤ s/2 := by
    calc
      _ ≤ c^2*(δ*s) := mul_le_mul_of_nonneg_left (hsmall none) (sq_nonneg c)
      _=(c^2*δ)*s := by ring
      _ ≤ (1/2)*s := mul_le_mul_of_nonneg_right hδc hs.le
      _=_ := by ring
  have hd2 : (c^2*norm τ (q*(p-t • (1:M))*q))^2 ≤ s^2/4 := by
    calc
      _ ≤ (s/2)^2 := (sq_le_sq₀ (mul_nonneg (sq_nonneg c) (norm_nonneg τ _)) (by positivity)).mpr hd
      _=_ := by ring
  have hqt4 : (τ q).re/4<(τ f).re := by
    rw [hs2] at hd2
    have hh := hker.trans hd2
    linarith only [hh,hqt]
  refine ⟨f,hN N hpN hqN,hf,hfp,lt_trans (by positivity) hqt4,hfq.trans_lt hqη,?_⟩
  intro j
  have hnorm : norm τ (f*x j*f) ≤ (ε/2)*s := by
    calc
      _ ≤ c^2*norm τ (q*x j*q)+(1+c)*‖x j‖*c^2*norm τ (q*(p-t • (1:M))*q) :=
        hcomp (x j) (hpx j) (hxp j)
      _ ≤ c^2*(δ*s)+(1+c)*B*c^2*(δ*s) := by
        gcongr
        · exact hsmall (some j)
        · exact norm_nonneg τ _
        · exact hxB j
        · exact hsmall none
      _=(K*δ)*s := by dsimp [K]; ring
      _ ≤ (ε/2)*s := mul_le_mul_of_nonneg_right hδK hs.le
  calc
    _ ≤ ((ε/2)*s)^2 := (sq_le_sq₀ (norm_nonneg τ _) (by positivity)).mpr hnorm
    _=ε^2*((τ q).re/4) := by rw [mul_pow,hs2]; ring
    _<ε^2*(τ f).re := mul_lt_mul_of_pos_left hqt4 (sq_pos_of_pos hε)

end Quantization

end Kadison.RelativeCornerQuantization

end

end
end

end OAI
