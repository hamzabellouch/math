import OAI.Combinatorics.SparsestCut.ChartKernel

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartAngles
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} {κ : Type u3} [Fintype ι] [Fintype κ]

def distance (g : κ → E) (q ε a b : ℝ) (θ η : E) (α β : κ → ℝ) : ℝ :=
  Profile.kernel g q ε a b θ θ α α+Profile.kernel g q ε a b η η β β-
    2*Profile.kernel g q ε a b θ η α β

lemma correction (g : κ → E) {q ε a b A : ℝ} (hε : 0≤ε) (ha : 0<a) (hab : a≤b)
    (hA : 0≤A) (θ η : E) (α β : κ → ℝ)
    (hα : ∀ i, |α i|≤A) (hβ : ∀ i, |β i|≤A) :
    |distance g q ε a b θ η α β-distance g q ε a b θ η 0 0| ≤
      4*(ε*(Fintype.card κ:ℝ)*(A^2+2*A)*Real.log (b/a)) := by
  have h1 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA θ θ α α hα hα)
  have h2 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA η η β β hβ hβ)
  have h3 := abs_le.mp (Profile.kernel_correction (q := q) g hε ha hab hA θ η α β hα hβ)
  unfold distance
  rw [abs_le]
  constructor <;> linarith

omit [InnerProductSpace ℝ E] in
lemma position_error (x y x' y' : E) {R : ℝ} (hx : ‖x-x'‖≤R) (hy : ‖y-y'‖≤R) :
    |‖x-y‖-‖x'-y'‖|≤2*R := by
  have he : (x-y)-(x'-y')=(x-x')-(y-y') := by abel
  calc
    _ ≤ ‖(x-y)-(x'-y')‖ := abs_norm_sub_norm_le _ _
    _ = ‖(x-x')-(y-y')‖ := by rw [he]
    _ ≤ ‖x-x'‖+‖y-y'‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma rounded_distance_error (g : κ → E) {q ε a b A R T : ℝ}
    (hq : 0≤q) (hε : 0≤ε) (ha : 0<a) (hab : a≤b) (hA : 0≤A)
    (θ η θ' η' : E) (α β : κ → ℝ) (hα : ∀ i, |α i|≤A) (hβ : ∀ i, |β i|≤A)
    (hθ : ‖θ-θ'‖≤R) (hη : ‖η-η'‖≤R) (hT : ‖η-θ‖≤T) :
    |distance g q ε a b θ η α β-KernelApprox.cstar*q*‖η'-θ'‖| ≤
      q*(2*a+T^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a)+
        4*(ε*(Fintype.card κ:ℝ)*(A^2+2*A)*Real.log (b/a))+2*KernelApprox.cstar*q*R := by
  have hb := MetricKernel.base_distance_error g hq hε ha hab θ η
  change |distance g q ε a b θ η 0 0-KernelApprox.cstar*q*‖η-θ‖| ≤ _ at hb
  have hc := correction (q := q) g hε ha hab hA θ η α β hα hβ
  have hp := position_error η θ η' θ' hη hθ
  have hT0 : 0≤T := (norm_nonneg _).trans hT
  have hbb : q*(2*a+‖η-θ‖^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a) ≤
      q*(2*a+T^2/b)+4*ε*(Fintype.card κ:ℝ)*Real.log (b/a) := by
    have hb0 : 0≤b := ha.le.trans hab
    gcongr
  have hcp : 0 ≤ KernelApprox.cstar*q := mul_nonneg KernelApprox.cstar_pos.le hq
  have hpe : |KernelApprox.cstar*q*(‖η-θ‖-‖η'-θ'‖)|≤2*KernelApprox.cstar*q*R := by
    rw [abs_mul,abs_of_nonneg hcp]
    calc
      _ ≤ KernelApprox.cstar*q*(2*R) := mul_le_mul_of_nonneg_left hp hcp
      _ = _ := by ring
  have hb' := abs_le.mp (hb.trans hbb)
  have hc' := abs_le.mp hc
  have hp' := abs_le.mp hpe
  change |distance g q ε a b θ η 0 0-KernelApprox.cstar*q*‖η-θ‖| ≤ _ at hb
  rw [abs_le]
  constructor <;> nlinarith

omit [InnerProductSpace ℝ E] [Fintype ι] in

lemma global_angle {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : ι → H) (θ : ι → E) {c e : ℝ} (hc : 0≤c) (_he : 0≤e)
    (hd : ∀ v w, |‖P v-P w‖^2-c*‖θ v-θ w‖|≤e) (v z y : ι) :
    -(3*e/2) ≤ inner ℝ (P v-P z) (P y-P z) := by
  have h1 := abs_le.mp (hd v z)
  have h2 := abs_le.mp (hd y z)
  have h3 := abs_le.mp (hd v y)
  have htri : ‖θ v-θ y‖≤‖θ v-θ z‖+‖θ y-θ z‖ := by
    have := norm_add_le (θ v-θ z) (θ z-θ y)
    rw [sub_add_sub_cancel,norm_sub_rev (θ z) (θ y)] at this
    exact this
  have hm := mul_le_mul_of_nonneg_left htri hc
  have hid : ‖P v-P z‖^2+‖P y-P z‖^2-‖P v-P y‖^2 =
      2*inner ℝ (P v-P z) (P y-P z) := by
    have he : P v-P y=(P v-P z)-(P y-P z) := by abel
    rw [he,norm_sub_sq_real (P v-P z) (P y-P z)]; ring
  nlinarith

end UniformSparsestCut.ChartAngles

namespace UniformSparsestCut.ChartAngles
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)
lemma segment_norm_le {X : Type u5} {Y : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y)
    (x x' : X) {R t : ℝ} (hx : ‖L x‖≤R) (hx' : ‖L x'‖≤R) (ht : t∈Icc (0:ℝ) 1) :
    ‖L (x+t • (x'-x))‖≤R := by
  have he : x+t • (x'-x)=(1-t) • x+t • x' := by module
  rw [he,map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(1-t) • L x‖+‖t • L x'‖ := norm_add_le _ _
    _ = (1-t)*‖L x‖+t*‖L x'‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg ht.1]
    _ ≤ (1-t)*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)) (mul_le_mul_of_nonneg_left hx' ht.1)
    _ = R := by ring

lemma local_profile (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    {q k ε a b T R γ : ℝ} (hq : 0<q) (hk : 0≤k) (hk1 : k≤1)
    (hε : 0<ε) (ha : 0<a) (hab : a≤b) (hT : 0≤T) (hR : 0≤R) (hγ : 0≤γ)
    (hkq : k=q^2/(N:ℝ)) (hg : ∀ s i, ‖g s i‖≤2*q)
    (hB : ∀ s i, ‖B s (EuclideanSpace.single i 1)‖≤4*k)
    (hf : ∀ (s : Fin S) (w : E), ‖w‖≤2*T/a →
      ‖Real.exp (-‖w‖^2/2) • w-((N:ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) w) • g s i‖≤γ)
    (s t : Fin S) (x x' y : F)
    (hx : ‖B s x‖≤T) (hx' : ‖B s x'‖≤T) (hy : ‖B t y‖≤T)
    (hrx : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x‖≤R)
    (hrx' : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g s i)) (B s) x'‖≤R)
    (hry : ‖ChartKernel.residual (FrameCharts.chart (fun i => q⁻¹ • g t i)) (B t) y‖≤R) :
    |Profile.kernel (fun j : Fin S × Fin N => g j.1 j.2) q ε a b
        (B s x') (B t y) (ChartKernel.alpha g B q k ε s x') (ChartKernel.alpha g B q k ε t y)-
      Profile.kernel (fun j : Fin S × Fin N => g j.1 j.2) q ε a b
        (B s x) (B t y) (ChartKernel.alpha g B q k ε s x) (ChartKernel.alpha g B q k ε t y)| ≤
      ((k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*(k/ε*R))*Real.log (b/a)+
        (ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+(k/ε*R)^2+2*(k/ε*R)))/a)*
          (∑ i, |x' i-x i|) := by
  let H : ℝ := ∑ i : Fin N, |x' i-x i|
  let A : ℝ := k/ε*R
  let C : ℝ := k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*A
  let D : ℝ := ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+A^2+2*A)
  have hH : 0≤H := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hA : 0≤A := by dsimp [A]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hθ (z : ℝ) (hz : z∈Icc (0:ℝ) 1) : ‖B s (x+z • (x'-x))‖≤T := segment_norm_le (B s) x x' hx hx' hz
  have hα (z : ℝ) (hz : z∈Icc (0:ℝ) 1) (j : Fin S × Fin N) :
      |ChartKernel.alpha g B q k ε s (x+z • (x'-x)) j|≤A :=
    ChartKernel.alpha_norm_bound g B hk hε s _ (segment_norm_le _ x x' hrx hrx' hz) j
  have hβ (j : Fin S × Fin N) : |ChartKernel.alpha g B q k ε t y j|≤A :=
    ChartKernel.alpha_norm_bound g B hk hε t y hry j
  have hv : ‖B s (x'-x)‖≤(4*k)*H := by
    simpa only [PiLp.sub_apply,H] using ChartKernel.norm_linear_le_l1 (B s) (by positivity : 0≤4*k) (hB s) (x'-x)
  have hd (z : ℝ) (hz : z∈Icc (0:ℝ) 1) (σ : ℝ) (hσ : σ∈Icc a b) :
      |Profile.differential (fun j : Fin S × Fin N => g j.1 j.2) q ε σ
        (B s x+z • B s (x'-x)) (B t y) (B s (x'-x))
        (fun j => ChartKernel.alpha g B q k ε s x j+z*ChartKernel.alpha g B q k ε s (x'-x) j)
        (ChartKernel.alpha g B q k ε t y) (ChartKernel.alpha g B q k ε s (x'-x))| ≤
        (C*H)/σ+(D*H)/σ^2 := by
    have hp : 0<σ := ha.trans_le hσ.1
    have he : B s x+z • B s (x'-x)=B s (x+z • (x'-x)) := by simp
    have hw : ‖(σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))‖≤2*T/a := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← div_eq_inv_mul]
      calc
        _ ≤ (2*T)/σ := div_le_div_of_nonneg_right
          ((norm_sub_le _ _).trans (by linarith [hθ z hz])) hp.le
        _ ≤ (2*T)/a := div_le_div_of_nonneg_left (by positivity) ha hσ.1
    have hfreq := hf s ((σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))) hw
    have hf' : ‖Real.exp (-‖(σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x)))‖^2/2) •
        ((σ⁻¹:ℝ) • (B t y-B s (x+z • (x'-x))))-
        ((Fintype.card (Fin N):ℝ)⁻¹) • ∑ i, Real.sin (inner ℝ (g s i) (B t y-B s (x+z • (x'-x)))/σ) • g s i‖≤γ := by
      simpa only [real_inner_smul_right,div_eq_inv_mul,Fintype.card_fin] using hfreq
    rw [he,← ChartKernel.alpha_linear]
    have hb := MetricKernel.full_differential_bound g s (B s (x+z • (x'-x))) (B t y)
      (B s (x'-x)) (fun i => (x'-x) i) (ChartKernel.alpha g B q k ε s (x+z • (x'-x)))
      (ChartKernel.alpha g B q k ε t y) hq hε hp (by simpa using hkq)
      (by positivity : 0≤2*q) hA (by positivity : 0≤4*k) hH (by positivity : 0≤9*k/ε) hγ hg hv
      (by simp only [PiLp.sub_apply,H]; exact le_rfl) (hα z hz) hβ
      (fun j => ChartKernel.alpha_derivative_bound g B hq hk hk1 hε s (x'-x)
        (by simp only [PiLp.sub_apply,H]; exact le_rfl) (hg s) (hB s) j) hf'
    convert! hb using 1 ; simp only [C,D,Fintype.card_fin,A]
  have hl := Profile.kernel_segment_bound (fun j : Fin S × Fin N => g j.1 j.2)
    ha hab (mul_nonneg hD hH) (B s x) (B t y) (B s (x'-x))
    (ChartKernel.alpha g B q k ε s x) (ChartKernel.alpha g B q k ε t y)
    (ChartKernel.alpha g B q k ε s (x'-x)) hd
  have heθ : B s x+B s (x'-x)=B s x' := by rw [map_sub]; abel
  have heα : (fun j => ChartKernel.alpha g B q k ε s x j+ChartKernel.alpha g B q k ε s (x'-x) j)=
      ChartKernel.alpha g B q k ε s x' := by
    have := ChartKernel.alpha_linear g B q k ε s x (x'-x) 1
    simpa only [one_smul,one_mul,add_sub_cancel] using this.symm
  rw [heθ,heα] at hl
  convert hl using 1 ; dsimp [C,D,A,H] ; ring

end UniformSparsestCut.ChartAngles

end

end OAI
