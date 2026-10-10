import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.TiltEnergy

namespace OAI

/-! Dyadic log moments and ground-state spectral tails. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

open Filter Topology
namespace PolynomialPEPS.Subvolume.Dyadic

lemma dyadic_linear_bound (g : ℝ → ℝ) (S r : ℝ) (hg0 : g 0=0)
    (hd : HasDerivAt g S 0)
    (hstep : ∀ t, |t|≤r → g t≤2*g (t/2))
    (u : ℝ) (hu : |u|≤r) : g u≤u*S := by
  by_cases hu0 : u=0
  · simp [hu0,hg0]
  let t := fun n : ℕ => u*(1/2:ℝ)^n
  have hsmall (n : ℕ) : |t n|≤r := by
    dsimp [t]
    rw [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))).trans hu
  have hnext (n : ℕ) : t (n+1)=t n/2 := by dsimp [t]; rw [pow_succ]; ring
  have hiter (n : ℕ) : g u≤(2:ℝ)^n*g (t n) := by
    induction n with
    | zero => simp [t]
    | succ n ih =>
      have hs := mul_le_mul_of_nonneg_left (hstep (t n) (hsmall n)) (pow_nonneg (by norm_num : (0:ℝ)≤2) n)
      calc
        g u≤2^n*g (t n) := ih
        _ ≤2^n*(2*g (t n/2)) := hs
        _ =2^(n+1)*g (t (n+1)) := by rw [hnext,pow_succ]; ring
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa [t] using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)))
  have htn : ∀ n, t n≠0 := fun n => mul_ne_zero hu0 (pow_ne_zero _ (by norm_num))
  have hts : Tendsto t atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨ht,Eventually.of_forall (fun n => htn n)⟩
  have hs := hd.tendsto_slope_zero.comp hts
  have hs' : Tendsto (fun n => g (t n)/(t n)) atTop (𝓝 S) := by
    simpa [hg0,div_eq_mul_inv,smul_eq_mul,Function.comp_def,mul_comm] using hs
  have heq (n : ℕ) : (2:ℝ)^n*g (t n)=u*(g (t n)/(t n)) := by
    have hprod : (2:ℝ)^n*t n=u := by
      dsimp [t]
      rw [mul_left_comm,← mul_pow]
      norm_num
    apply (mul_right_cancel₀ (htn n))
    rw [mul_assoc u,div_mul_cancel₀ _ (htn n)]
    calc
      2^n*g (t n)*t n=(2^n*t n)*g (t n) := by ring
      _ = _ := by rw [hprod]
  have hl : Tendsto (fun n => (2:ℝ)^n*g (t n)) atTop (𝓝 (u*S)) := by
    simpa only [heq] using (tendsto_const_nhds.mul hs')
  exact ge_of_tendsto hl (Eventually.of_forall hiter)

theorem quadratic_bound (L : ℝ → ℝ) (S C r : ℝ) (hL0 : L 0=0)
    (hd : HasDerivAt L S 0)
    (hstep : ∀ t, |t|≤r → L t≤2*L (t/2)+C*t^2)
    (u : ℝ) (hu : |u|≤r) : L u≤u*S+2*C*u^2 := by
  let g := fun t => L t-2*C*t^2
  have hg0 : g 0=0 := by simp [g,hL0]
  have hg : HasDerivAt g S 0 := by
    have hz : HasDerivAt (fun t : ℝ => 2*C*t^2) 0 0 := by
      convert (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (2*C)) using 1 <;> norm_num
    convert hd.sub hz using 1
    simp only [sub_zero]
  have hgs (t : ℝ) (ht : |t|≤r) : g t≤2*g (t/2) := by
    have hs := hstep t ht
    dsimp [g]
    nlinarith only [hs]
  have hb := dyadic_linear_bound g S r hg0 hg hgs u hu
  dsimp [g] at hb
  linarith

end PolynomialPEPS.Subvolume.Dyadic

open scoped BigOperators
namespace PolynomialPEPS.Subvolume.MGFScalar
variable {ι : Type*} [Fintype ι]

def moment (p : ι → ℝ) (u : ℝ) : ℝ := ∑ i, (p i)^(1-u)
def entropy (p : ι → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)
def logMoment (p : ι → ℝ) (u : ℝ) : ℝ := Real.log (moment p u)

lemma moment_zero (p : ι → ℝ) (hs : ∑ i,p i=1) : moment p 0=1 := by
  simpa [moment] using hs

lemma moment_pos (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1) (u : ℝ) :
    0 < moment p u := by
  classical
  have hpos : 0<∑ i,p i := by rw [hs]; norm_num
  obtain ⟨i,hi,hpi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hp i)).mp hpos
  exact Finset.sum_pos' (fun j _ => Real.rpow_nonneg (hp j) _) ⟨i,hi,Real.rpow_pos_of_pos hpi _⟩

lemma summand_derivative (p : ℝ) (hp : 0≤p) :
    HasDerivAt (fun u : ℝ => p^(1-u)) (Real.negMulLog p) 0 := by
  by_cases hp0 : p=0
  · subst p
    have he : (fun u : ℝ => (0:ℝ)^(1-u)) =ᶠ[𝓝 0] (fun _ => (0:ℝ)) := by
      filter_upwards [eventually_lt_nhds (by norm_num : (0:ℝ)<1)] with u hu
      exact Real.zero_rpow (by linarith)
    convert (hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq he using 1
    first | rfl | simp
  · have h := ((hasDerivAt_id (0:ℝ)).const_sub 1).const_rpow (lt_of_le_of_ne hp (Ne.symm hp0))
    convert h using 1 <;> first | rfl | simp [Real.negMulLog_def]
    ring

lemma moment_derivative (p : ι → ℝ) (hp : ∀ i, 0≤p i) :
    HasDerivAt (moment p) (entropy p) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => summand_derivative (p i) (hp i))
  convert h using 1 <;> rfl

lemma logMoment_zero (p : ι → ℝ) (hs : ∑ i,p i=1) : logMoment p 0=0 := by
  simp [logMoment,moment_zero p hs]

lemma logMoment_derivative (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1) :
    HasDerivAt (logMoment p) (entropy p) 0 := by
  have h := (moment_derivative p hp).log (moment_pos p hp hs 0).ne'
  rw [moment_zero p hs,div_one] at h
  convert h using 1
  rfl

lemma neg_log_one_sub_le (x : ℝ) (hx : 0≤x) (hx' : x≤1/2) :
    -Real.log (1-x)≤2*x := by
  have hp : 0<1-x := by linarith
  have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hb
  calc
    _ ≤ (1-x)⁻¹-1 := hb
    _ = x/(1-x) := by field_simp; ring
    _ ≤ 2*x := (div_le_iff₀ hp).mpr (by nlinarith)

lemma log_recurrence (p : ι → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1)
    (K u : ℝ) (hK : 0≤K) (hu : K*u^2≤1/2)
    (hgap : (1-K*u^2)*moment p u≤(moment p (u/2))^2) :
    logMoment p u≤2*logMoment p (u/2)+2*K*u^2 := by
  have hc : 0<1-K*u^2 := by linarith
  have hl := Real.log_le_log (mul_pos hc (moment_pos p hp hs u)) hgap
  rw [Real.log_mul hc.ne' (moment_pos p hp hs u).ne',Real.log_pow] at hl
  have hb := neg_log_one_sub_le (K*u^2) (mul_nonneg hK (sq_nonneg _)) hu
  dsimp [logMoment]
  nlinarith only [hl,hb]

theorem subgaussian_of_gap_recurrence (p : ι → ℝ) (hp : ∀ i, 0≤p i)
    (hs : ∑ i,p i=1) (K r : ℝ) (hK : 0≤K)
    (hsmall : ∀ u, |u|≤r → K*u^2≤1/2)
    (hgap : ∀ u, |u|≤r → (1-K*u^2)*moment p u≤(moment p (u/2))^2)
    (u : ℝ) (hu : |u|≤r) :
    logMoment p u≤u*entropy p+4*K*u^2 := by
  have h := Dyadic.quadratic_bound (logMoment p) (entropy p) (2*K) r
    (logMoment_zero p hs) (logMoment_derivative p hp hs)
    (fun t ht => log_recurrence p hp hs K t hK (hsmall t ht) (hgap t ht)) u hu
  nlinarith only [h]

end PolynomialPEPS.Subvolume.MGFScalar

namespace PolynomialPEPS.Subvolume.HermitianReplacement
open scoped BigOperators
open Matrix
variable {L q : ℕ}

def symmetrize (A : Operator L q) : Operator L q := (1/2:ℂ) • (A+star A)

lemma symmetrize_hermitian (A : Operator L q) : (symmetrize A).IsHermitian := by
  change star (symmetrize A)=symmetrize A
  simp [symmetrize,star_smul,star_add,add_comm]

lemma symmetrize_supported (A : Operator L q) (S : Finset (Vertex L)) (hA : SupportedOn A S) :
    SupportedOn (symmetrize A) S := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨(1/2:ℂ) • (B+star B),?_⟩
  change (1/2:ℂ) • ((localLiftHom S) B+star ((localLiftHom S) B))=
    (localLiftHom S) ((1/2:ℂ) • (B+star B))
  rw [map_smul,map_add,map_star]

lemma symmetrize_norm (A : Operator L q) : opNorm (symmetrize A)≤opNorm A := by
  unfold opNorm asMap symmetrize
  rw [map_smul,map_add,map_star,norm_smul]
  have hc : ‖(1/2:ℂ)‖=1/2 := by norm_num
  rw [hc]
  calc
    _ ≤ (1/2:ℝ)*(‖Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) A‖+‖star (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) A)‖) := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint.norm_map]; ring

lemma symmetrize_self (A : Operator L q) (hA : A.IsHermitian) : symmetrize A=A := by
  rw [symmetrize,hA.star_eq,← two_smul ℂ A,smul_smul]
  norm_num

lemma symmetrize_sum {ι : Type*} [Fintype ι] (A : ι → Operator L q) :
    symmetrize (∑ i,A i)=∑ i,symmetrize (A i) := by
  simp only [symmetrize,star_sum,Finset.sum_add_distrib,smul_add,Finset.smul_sum]

lemma symmetrize_add (A B : Operator L q) : symmetrize (A+B)=symmetrize A+symmetrize B := by
  simp only [symmetrize,star_add,smul_add]
  abel

lemma replacement_preserves_H (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (hH : (Hamiltonian hv he).IsHermitian) :
    Hamiltonian (fun v => symmetrize (hv v)) (fun e => symmetrize (he e))=Hamiltonian hv he := by
  calc
    _ = symmetrize (Hamiltonian hv he) := by simp only [Hamiltonian,symmetrize_add,symmetrize_sum]
    _ = _ := symmetrize_self _ hH

end PolynomialPEPS.Subvolume.HermitianReplacement

namespace PolynomialPEPS.Subvolume.GroundMGF
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.GroundTilt PolynomialPEPS.Subvolume.MGFScalar PolynomialPEPS.Subvolume.SpectralCurve
open PolynomialPEPS.Subvolume.HermitianReplacement PolynomialPEPS.Subvolume.OptimizerNeutral
variable {L q : ℕ}

lemma gap_moment_recurrence (hq : 0<q) (J Δ E₀ : ℝ) (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity Ω X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : |u|≤1/4) :
    (1-(32*(q:ℝ)^2*J*(boundaryCard X:ℝ)/Δ)*u^2)*moment p u≤(moment p (u/2))^2 := by
  let vh := fun v => symmetrize (hv v)
  let eh := fun e => symmetrize (he e)
  have heq : Hamiltonian vh eh=Hamiltonian hv he := replacement_preserves_H hv he hH.2.2
  have hvs (v : Vertex L) : SupportedOn (vh v) {v} := symmetrize_supported _ _ (hH.1 v).1
  have hes (e : Edge L) : SupportedOn (eh e) (EdgeSites e) := symmetrize_supported _ _ (hH.2.1 e).1
  have hn (e : Edge L) : opNorm (eh e)≤J := (symmetrize_norm _).trans (hH.2.1 e).2
  have hb := tilt_excitation_bound hq X Ω U p hp hρ u hu vh eh hvs hes
    (fun e => symmetrize_hermitian (he e)) J E₀ hJ hn (by rwa [heq])
  rw [heq] at hb
  have hf := gap_fidelity (Hamiltonian hv he) Ω (tilt X U p u Ω) E₀ Δ
    (32*(q:ℝ)^2*J*(boundaryCard X:ℝ)*u^2) hgap hΔ hb
  have hu1 : u<1 := by have h := (abs_le.mp hu).2; linarith
  rw [tilt_norm_sq X Ω U p hp hρ u hu1,tilt_pairing_eq X Ω U p hp hρ u hu1,
    Complex.norm_real,Real.norm_eq_abs,sq_abs] at hf
  change (1-32*(q:ℝ)^2*J*(boundaryCard X:ℝ)*u^2/Δ)*moment p u≤(moment p (u/2))^2 at hf
  convert hf using 1
  ring

theorem log_moment_bound (hq : 0<q) (J Δ E₀ : ℝ) (hJ : 0≤J) (hΔ : 0<Δ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) (Ω : State L q)
    (hH : IsGridHamiltonian J hv he)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω)
    (hgap : FullSystemGap (Hamiltonian hv he) Ω E₀ Δ)
    (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i) (hs : ∑ i,p i=1)
    (hρ : reducedDensity Ω X=spectralHom U (fun i => (p i:ℂ)))
    (r : ℝ) (hr : r≤1/4)
    (hsmall : (32*(q:ℝ)^2*J*(boundaryCard X:ℝ)/Δ)*r^2≤1/2)
    (u : ℝ) (hu : |u|≤r) :
    logMoment p u≤u*entropy p+(128*(q:ℝ)^2*J*(boundaryCard X:ℝ)/Δ)*u^2 := by
  let K := 32*(q:ℝ)^2*J*(boundaryCard X:ℝ)/Δ
  have hK : 0≤K := by dsimp [K]; positivity
  have hb := subgaussian_of_gap_recurrence p hp hs K r hK
    (fun t ht => by simpa only [sq_abs] using (mul_le_mul_of_nonneg_left (sq_le_sq₀ (abs_nonneg t) (le_trans (abs_nonneg t) ht) |>.mpr ht) hK).trans hsmall)
    (fun t ht => gap_moment_recurrence hq J Δ E₀ hJ hΔ hv he Ω hH hg hgap X U p hp hρ t (ht.trans hr)) u hu
  dsimp [K] at hb
  convert hb using 1
  ring

end PolynomialPEPS.Subvolume.GroundMGF

end

end OAI
