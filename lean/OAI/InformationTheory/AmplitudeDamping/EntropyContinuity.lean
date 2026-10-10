import OAI.InformationTheory.AmplitudeDamping.StateEntropy

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

def frobVector (A : Matrix ι κ ℂ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun ik ↦ A ik.1 ik.2)

theorem mass_eq_sum_normSq (A : Matrix ι κ ℂ) : mass A=∑ i, ∑ k, Complex.normSq (A i k) := by
  simp [mass,gram,Matrix.trace,Matrix.mul_apply,Complex.mul_conj]

theorem frobVector_norm (A : Matrix ι κ ℂ) : ‖frobVector A‖^2=mass A := by
  rw [EuclideanSpace.norm_sq_eq,mass_eq_sum_normSq]
  simp only [Fintype.sum_prod_type,frobVector,PiLp.toLp_apply,Complex.sq_norm]

omit [Fintype ι] [Fintype κ] in
theorem frobVector_add (A B : Matrix ι κ ℂ) : frobVector (A+B)=frobVector A+frobVector B := rfl
omit [Fintype ι] [Fintype κ] in
theorem frobVector_sub (A B : Matrix ι κ ℂ) : frobVector (A-B)=frobVector A-frobVector B := rfl

theorem frobVector_inner (A B : Matrix ι κ ℂ) :
    ⟪frobVector A,frobVector B⟫_ℝ=(Aᴴ*B).trace.re := by
  have hn := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at hn
  have hm : mass (A+B)=mass A+mass B+2*(Aᴴ*B).trace.re := by
    rw [mass_eq_sum_normSq,mass_eq_sum_normSq,mass_eq_sum_normSq]
    simp only [Matrix.add_apply,Complex.normSq_add,Finset.sum_add_distrib,← Finset.mul_sum]
    congr 1
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.star_def]
    ring
  linarith

variable [DecidableEq ι]

def IsProjection (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P*P=P

omit [DecidableEq ι] in
theorem IsProjection.posSemidef {P : Matrix ι ι ℂ} (hP : IsProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hP.1.eq,hP.2] at h

theorem IsProjection.complement {P : Matrix ι ι ℂ} (hP : IsProjection P) : IsProjection (1-P) := by
  refine ⟨(Matrix.isHermitian_one).sub hP.1, ?_⟩
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,hP.2]
  simp

omit [DecidableEq ι] in
theorem projection_orthogonal {P : Matrix ι ι ℂ} (hP : IsProjection P) (A B : Matrix ι κ ℂ) :
    ⟪frobVector (P*A),frobVector (B-P*B)⟫_ℝ=0 := by
  rw [frobVector_inner,Matrix.conjTranspose_mul,hP.1.eq,Matrix.mul_sub]
  have he : Aᴴ*P*(P*B)=Aᴴ*P*B := by
    rw [← Matrix.mul_assoc _ P,Matrix.mul_assoc Aᴴ P P,hP.2]
  rw [he,sub_self,Matrix.trace_zero,Complex.zero_re]

omit [DecidableEq ι] in
theorem projection_mass_decomposition {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A)+mass (A-P*A)=mass A := by
  have h := norm_add_sq_real (frobVector (P*A)) (frobVector (A-P*A))
  rw [← frobVector_add,projection_orthogonal hP A A,mul_zero,add_zero] at h
  have he : P*A+(A-P*A)=A := by abel
  rw [he,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

omit [DecidableEq ι] in
theorem projection_mass_le {P : Matrix ι ι ℂ} (hP : IsProjection P) (A : Matrix ι κ ℂ) :
    mass (P*A) ≤ mass A := by
  have h := projection_mass_decomposition hP A
  linarith [mass_nonneg (A-P*A)]

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem shannon_le_log_card [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card ι) := by
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by dsimp [d]; exact_mod_cast (Fintype.card_pos (α := ι))
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : ι ↦ d⁻¹) (p := p)
    (fun _ _ ↦ inv_nonneg.mpr hd.le)
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_inv_cancel₀ hd.ne')
    (fun i _ ↦ (show p i ∈ Set.Ici 0 from hp i))
  simp only [smul_eq_mul,← Finset.mul_sum,hs,mul_one,Real.negMulLog,Real.log_inv] at h
  have hh := mul_le_mul_of_nonneg_left h hd.le
  dsimp only [d] at *
  calc
    _ = (Fintype.card ι:ℝ) * ((Fintype.card ι:ℝ)⁻¹ * ∑ i, Real.negMulLog (p i)) := by
      rw [← mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
    _ ≤ _ := hh
    _ = _ := by field_simp

theorem entropy_le_log_card [Nonempty ι] {A : Matrix ι ι ℂ} (hA : IsState A) :
    entropy A ≤ Real.log (Fintype.card ι) := by
  rw [entropy_eq_sum hA.1.isHermitian]
  exact shannon_le_log_card _ hA.1.eigenvalues_nonneg (spectral_weights_sum hA)

theorem state_normalize_trace {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) (htr : A.trace=(t:ℂ)) : IsState (t⁻¹ • A) := by
  refine ⟨hA.smul (inv_nonneg.mpr ht.le), ?_⟩
  rw [Matrix.trace_smul,htr]
  simp [Complex.real_smul,ht.ne']

/-- Entropy continuity from a positive common-mixture coupling. -/
theorem entropy_coupling_bound [Nonempty ι] {A B U V : Matrix ι ι ℂ}
    (hA : IsState A) (hB : IsState B) (hU : U.PosSemidef) (hV : V.PosSemidef)
    {t : ℝ} (ht : 0 < t) (htrU : U.trace=(t:ℂ)) (htrV : V.trace=(t:ℂ))
    (heq : A+U=B+V) :
    entropy A-entropy B ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := by
  let a : ℝ := (1+t)⁻¹
  let b : ℝ := t/(1+t)
  have ht1 : 0 < 1+t := by positivity
  have ha : 0 ≤ a := inv_nonneg.mpr ht1.le
  have hb : 0 ≤ b := div_nonneg ht.le ht1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have hu := state_normalize_trace hU ht htrU
  have hv := state_normalize_trace hV ht htrV
  have he : a • A+b • (t⁻¹ • U)=a • B+b • (t⁻¹ • V) := by
    have hba : b*t⁻¹=a := by dsimp [a,b]; field_simp
    simp only [smul_smul,hba,← smul_add,heq]
  have hlo := concaveOn_entropy.2 hA.1 hu.1 ha hb hab
  have hup := entropy_mixture_upper (fun s : Fin 2 ↦ if s=0 then a else b)
    (fun s : Fin 2 ↦ if s=0 then B else t⁻¹ • V)
    (by intro s; split_ifs <;> assumption)
    (by intro s; split_ifs <;> assumption)
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2) ≠ 0 by decide,ite_false] at hup
  rw [he] at hlo
  have hU0 := entropy_nonneg hu
  have hVmax := entropy_le_log_card hv
  have hm := mul_le_mul_of_nonneg_left hVmax hb
  have hh : Real.negMulLog a+Real.negMulLog b=Real.binEntropy b := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    have heab : a=1-b := by linarith
    rw [heab]; ring
  have htotal : a*(entropy A-entropy B) ≤ b*Real.log (Fintype.card ι)+Real.binEntropy b := by
    change a*entropy A+b*entropy (t⁻¹ • U) ≤ _ at hlo
    nlinarith [mul_nonneg hb hU0]
  have hh' := mul_le_mul_of_nonneg_left htotal ht1.le
  dsimp only [a,b] at hh'
  have hc : (1+t)*((1+t)⁻¹*(entropy A-entropy B)) = entropy A-entropy B := by
    rw [← mul_assoc,mul_inv_cancel₀ ht1.ne',one_mul]
  rw [hc,mul_add] at hh'
  have hc' : (1+t)*(t/(1+t)*Real.log (Fintype.card ι))=t*Real.log (Fintype.card ι) := by
    field_simp
  rwa [hc'] at hh'

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

theorem mass_real_smul (a : ℝ) (A : Matrix ι κ ℂ) : mass (a • A)=a^2*mass A := by
  rw [← frobVector_norm,← frobVector_norm]
  have he : frobVector (a • A)=a • frobVector A := rfl
  rw [he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem mass_add (A B : Matrix ι κ ℂ) :
    mass (A+B)=mass A+mass B+2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_add_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_add,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem mass_sub (A B : Matrix ι κ ℂ) :
    mass (A-B)=mass A+mass B-2*⟪frobVector A,frobVector B⟫_ℝ := by
  have h := norm_sub_sq_real (frobVector A) (frobVector B)
  rw [← frobVector_sub,frobVector_norm,frobVector_norm,frobVector_norm] at h
  linarith

theorem gram_posSemidef (A : Matrix ι κ ℂ) : (gram A).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

theorem gram_trace (A : Matrix ι κ ℂ) : (gram A).trace=(mass A:ℂ) := by
  exact Complex.ext (by rfl) (by simpa using (Complex.nonneg_iff.mp (gram_posSemidef A).trace_nonneg).2.symm)

variable [DecidableEq ι]

/-- Quantitative entropy comparison from close normalized Gram factors. -/
theorem factor_entropy_bound [Nonempty ι] (X Y : Matrix ι κ ℂ)
    (hX : mass X=1) (hY : mass Y=1) {ε : ℝ} (hε : 0 < ε) :
    entropy (gram X)-entropy (gram Y) ≤
      (mass (X-Y)/(4*ε)+ε)*Real.log (Fintype.card ι)+
        (1+mass (X-Y)/(4*ε)+ε)*Real.log 2 := by
  let D := X-Y
  let S := X+Y
  have hDS : ⟪frobVector D,frobVector S⟫_ℝ=0 := by
    dsimp [D,S]
    rw [frobVector_sub,frobVector_add,inner_sub_left,inner_add_right,inner_add_right,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_comm (frobVector Y),
      frobVector_norm,frobVector_norm,hX,hY]
    ring
  have hsum : mass D+mass S=4 := by
    dsimp [D,S]; rw [mass_add,mass_sub,hX,hY]; ring
  have hSle : mass S ≤ 4 := by linarith [mass_nonneg D]
  let c : ℝ := (4*ε)⁻¹
  let U : Matrix ι ι ℂ := c • gram (D-ε • S)
  let V : Matrix ι ι ℂ := c • gram (D+ε • S)
  let t : ℝ := c*(mass D+ε^2*mass S)
  have hc : 0 < c := inv_pos.mpr (by positivity)
  have htm : 0 < mass D+ε^2*mass S := by
    have hd := mass_nonneg D
    have hs := mass_nonneg S
    have hes : 0 < ε^2 := sq_pos_of_pos hε
    by_cases hdz : mass D=0
    · have hspos : 0 < mass S := by linarith
      exact add_pos_of_nonneg_of_pos hd (mul_pos hes hspos)
    · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hd (Ne.symm hdz)) (mul_nonneg hes.le hs)
  have ht : 0 < t := mul_pos hc htm
  have hin : ⟪frobVector D,frobVector (ε • S)⟫_ℝ=0 := by
    change ⟪frobVector D,ε • frobVector S⟫_ℝ=0
    rw [real_inner_smul_right,hDS,mul_zero]
  have hmU : mass (D-ε • S)=mass D+ε^2*mass S := by rw [mass_sub,mass_real_smul,hin]; ring
  have hmV : mass (D+ε • S)=mass D+ε^2*mass S := by rw [mass_add,mass_real_smul,hin]; ring
  have htrU : U.trace=(t:ℂ) := by
    dsimp [U,t]; rw [Matrix.trace_smul,gram_trace,hmU]; simp [Complex.real_smul]; ring
  have htrV : V.trace=(t:ℂ) := by
    dsimp [V,t]; rw [Matrix.trace_smul,gram_trace,hmV]; simp [Complex.real_smul]; ring
  have hUV : gram X+U=gram Y+V := by
    have hcε : c*(4*ε)=1 := inv_mul_cancel₀ (by positivity)
    ext i j
    simp only [U,V,D,S,gram,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,star_sub,star_add,
      Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hcε' : (c:ℂ)*(4*ε)=1 := by exact_mod_cast hcε
    linear_combination -(X i k*(starRingEnd ℂ) (X j k)-Y i k*(starRingEnd ℂ) (Y j k))*hcε'
  have hA : IsState (gram X) := ⟨gram_posSemidef X, by rw [gram_trace,hX]; norm_num⟩
  have hB : IsState (gram Y) := ⟨gram_posSemidef Y, by rw [gram_trace,hY]; norm_num⟩
  have hb := entropy_coupling_bound hA hB ((gram_posSemidef _).smul hc.le)
    ((gram_posSemidef _).smul hc.le) ht htrU htrV hUV
  have htle : t ≤ mass (X-Y)/(4*ε)+ε := by
    dsimp [t,c,D]
    have haux : ε^2*mass S ≤ ε^2*4 := mul_le_mul_of_nonneg_left hSle (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left haux (inv_nonneg.mpr (show 0 ≤ 4*ε by positivity))
    have he : (4*ε)⁻¹*(mass (X-Y)+ε^2*4)=mass (X-Y)/(4*ε)+ε := by field_simp
    rw [← he]; nlinarith
  have hlog : 0 ≤ Real.log (Fintype.card ι) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := ι))
  have hint : Real.binEntropy (t/(1+t)) ≤ Real.log 2 := Real.binEntropy_le_log_two
  calc
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t)) := hb
    _ ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.log 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hint (by positivity))
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_right htle hlog
      have h2 := mul_le_mul_of_nonneg_right htle (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
      nlinarith

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

theorem mass_eq_zero (A : Matrix ι κ ℂ) : mass A=0 ↔ A=0 := by
  rw [← frobVector_norm,sq_eq_zero_iff,norm_eq_zero]
  constructor
  · intro h; ext i k; exact congrArg (fun v : EuclideanSpace ℂ (ι × κ) ↦ v (i,k)) h
  · intro h; subst A; rfl

theorem projection_inner {P : Matrix ι ι ℂ} (hP : IsProjection P) (X : Matrix ι κ ℂ) :
    ⟪frobVector X,frobVector (P*X)⟫_ℝ=mass (P*X) := by
  have h := projection_orthogonal hP X X
  rw [frobVector_sub,inner_sub_right,real_inner_self_eq_norm_sq,
    frobVector_norm,real_inner_comm] at h
  linarith

/-- Normalize a successful projection without losing more than twice its failure mass. -/
theorem exists_projected_factor {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (X B : Matrix ι κ ℂ) (hX : mass X=1) (hB : mass B=1) (hPB : P*B=B) :
    ∃ Y : Matrix ι κ ℂ, mass Y=1 ∧ P*Y=Y ∧ mass (X-Y) ≤ 2*(1-mass (P*X)) := by
  let p := mass (P*X)
  have hp0 : 0 ≤ p := mass_nonneg _
  have hp1 : p ≤ 1 := by simpa only [hX] using projection_mass_le hP X
  by_cases hp : p=0
  · refine ⟨B,hB,hPB,?_⟩
    have hz : P*X=0 := (mass_eq_zero _).mp hp
    have hi := projection_orthogonal hP B X
    rw [hPB,hz,sub_zero,real_inner_comm] at hi
    rw [mass_sub,hX,hB,hi]
    change 1+1-2*0 ≤ 2*(1-p)
    rw [hp]; norm_num
  · have hpp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpp
    let a : ℝ := (Real.sqrt p)⁻¹
    refine ⟨a • (P*X), ?_, ?_, ?_⟩
    · rw [mass_real_smul]
      change (Real.sqrt p)⁻¹^2*p=1
      rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
    · rw [Matrix.mul_smul,← Matrix.mul_assoc,hP.2]
    · rw [mass_sub,mass_real_smul,hX]
      have he : a^2*mass (P*X)=1 := by
        change (Real.sqrt p)⁻¹^2*p=1
        rw [inv_pow,Real.sq_sqrt hp0,inv_mul_cancel₀ hp]
      rw [he]
      change 1+1-2*⟪frobVector X,a • frobVector (P*X)⟫_ℝ ≤ 2*(1-p)
      rw [real_inner_smul_right,projection_inner hP X]
      have hsp : p ≤ Real.sqrt p := by nlinarith [Real.sq_sqrt hp0,(Real.sqrt_nonneg p)]
      have hprod : a*p=Real.sqrt p := by
        dsimp [a]
        calc
          _ = (Real.sqrt p)⁻¹ * (Real.sqrt p*Real.sqrt p) := by congr 1; nlinarith [Real.sq_sqrt hp0]
          _ = _ := by field_simp
      change 1+1-2*(a*p) ≤ 2*(1-p)
      rw [hprod]; linarith

end GAD

end

end OAI
