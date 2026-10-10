import Mathlib
import OAI.Probability.LogConcave.Numerics.Correction

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E]

lemma lipschitz_zero_shift {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) :
    LipschitzWith K (fun x => φ x-φ 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hφ.dist_le_mul x y

def nodeLp {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) (f : Lp E 2 ν) : Lp E 2 ν :=
  (lipschitz_zero_shift hφ).compLp (by simp) f + Lp.const 2 ν (φ 0)

lemma nodeLp_ae {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) (f : Lp E 2 ν) :
    (nodeLp hφ f : Ω → E)=ᵐ[ν] fun z => φ (f z) := by
  filter_upwards [Lp.coeFn_add ((lipschitz_zero_shift hφ).compLp (by simp) f)
      (Lp.const 2 ν (φ 0)),
    (lipschitz_zero_shift hφ).coeFn_compLp (by simp) f,
    Lp.coeFn_const 2 ν (φ 0)] with z hz hφz hc
  simp only [nodeLp,hz,Pi.add_apply,hφz,Function.comp_apply,hc,Function.const_apply,sub_add_cancel]

lemma nodeLp_lipschitz {K : ℝ≥0} {φ : E → E} (hφ : LipschitzWith K φ) :
    LipschitzWith K (nodeLp (ν:=ν) hφ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [nodeLp,dist_add_right] using
    ((lipschitz_zero_shift hφ).lipschitzWith_compLp (by simp)).dist_le_mul f g

variable [NormedSpace ℝ E] [Fintype I]

def stepLp (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a z : I → Lp E 2 ν) : I → Lp E 2 ν :=
  step w (fun j => nodeLp (hφ j)) a z

lemma stepLp_lipschitz (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) : LipschitzWith (A*K) (stepLp w φ hφ a) :=
  step_lipschitz w _ a hw (fun j => nodeLp_lipschitz (hφ j))

lemma stepLp_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a z : I → Lp E 2 ν) (i : I) :
    (stepLp w φ hφ a z i : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun j => a j ω) (fun j => z j ω) i := by
  classical
  have ha := Lp.coeFn_add (a i) (∑j,w i j • nodeLp (hφ j) (z j))
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => w i j • nodeLp (hφ j) (z j))
  have hm : ∀ᵐω ∂ν,∀j,(w i j • nodeLp (hφ j) (z j) : Lp E 2 ν) ω=
      w i j • φ j (z j ω) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (w i j) (nodeLp (hφ j) (z j)),nodeLp_ae (hφ j) (z j)] with ω h1 h2
    simp only [h1,Pi.smul_apply,h2]
  filter_upwards [ha,hs,hm] with ω h1 h2 h3
  simp only [stepLp,step,correction,Pi.add_apply,h1,h2,h3]

theorem rms_picard_defect (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Lp E 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D : ℝ} (hD : 0≤D) (he : ∀i,dist (stepLp w φ hφ a e i) (e i)≤D) (n : ℕ) :
    dist ((stepLp w φ hφ a)^[n] a) e≤2*D+(A*K:ℝ≥0)^n*dist a e := by
  apply iterate_defect (stepLp_lipschitz w φ hφ a hw) (by exact_mod_cast hq) a e hD
    ((dist_pi_le_iff hD).mpr he) n

section Inner
omit [NormedSpace ℝ E] [IsFiniteMeasure ν]
variable [InnerProductSpace ℝ E]

lemma lp_norm_sq_integral (f : Lp E 2 ν) : ‖f‖^2=∫ω,‖f ω‖^2 ∂ν := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma nodewise_rms_le {f g : Lp E 2 ν} {B : ℝ} (hB : 0≤B)
    (h : (∫ω,‖f ω-g ω‖^2 ∂ν)≤B^2) : dist f g≤B := by
  rw [dist_eq_norm]
  have he : ‖f-g‖^2=∫ω,‖f ω-g ω‖^2 ∂ν := by
    rw [lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with ω hω
    simp only [hω,Pi.sub_apply]
  nlinarith [norm_nonneg (f-g)]
end Inner
end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace

variable {Ω E I : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

omit [IsFiniteMeasure ν] in
lemma lp_rms_eq (f g : Lp E 2 ν) {u v : Ω → E}
    (hf : (f : Ω → E)=ᵐ[ν] u) (hg : (g : Ω → E)=ᵐ[ν] v) :
    Integrable (fun ω => ‖u ω-v ω‖^2) ν ∧
      (∫ω,‖u ω-v ω‖^2 ∂ν)=dist f g^2 := by
  have he : (fun ω => (f-g : Lp E 2 ν) ω)=ᵐ[ν] fun ω => u ω-v ω := by
    filter_upwards [Lp.coeFn_sub f g,hf,hg] with ω h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
  have hi := (Lp.memLp (f-g)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hn : (fun ω => ‖(f-g : Lp E 2 ν) ω‖^2)=ᵐ[ν] fun ω => ‖u ω-v ω‖^2 :=
    he.fun_comp (fun z => ‖z‖^2)
  refine ⟨hi.congr hn,?_⟩
  rw [dist_eq_norm,lp_norm_sq_integral]
  exact integral_congr_ae hn.symm

lemma iterateLp_nodes_ae (w : I → I → ℝ) (φ : I → E → E) {K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a : I → Ω → E) (aLp : I → Lp E 2 ν)
    (ha : ∀i,(aLp i : Ω → E)=ᵐ[ν] a i) (N : ℕ) (i : I) :
    ((stepLp w φ hφ aLp)^[N] aLp i : Ω → E)=ᵐ[ν]
      fun ω => nodes w φ (fun ω j => a j ω) N ω i := by
  induction N generalizing i with
  | zero => simpa only [Function.iterate_zero_apply,nodes] using ha i
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have hia : ∀ᵐω ∂ν,∀j,aLp j ω=a j ω := ae_all_iff.mpr ha
    have hii : ∀ᵐω ∂ν,∀j,((stepLp w φ hφ aLp)^[N] aLp j : Ω → E) ω=
        nodes w φ (fun ω j => a j ω) N ω j := ae_all_iff.mpr ih
    filter_upwards [stepLp_ae w φ hφ aLp ((stepLp w φ hφ aLp)^[N] aLp) i,hia,hii] with ω h1 h2 h3
    simp only [h1,nodes,step,correction,Pi.add_apply,h2,h3]

theorem nodes_rms (w : I → I → ℝ) (φ : I → E → E) {A K : ℝ≥0}
    (hφ : ∀i,LipschitzWith K (φ i)) (a e : I → Ω → E)
    (ha : ∀i,MemLp (a i) 2 ν) (he : ∀i,MemLp (e i) 2 ν)
    (hw : ∀i,∑j,|w i j|≤A) (hq : (A*K:ℝ≥0)≤1/2)
    {D H : ℝ} (hD : 0≤D) (hH : 0≤H)
    (hdef : ∀i,(∫ω,‖step w φ (fun j => a j ω) (fun j => e j ω) i-e i ω‖^2 ∂ν)≤D^2)
    (hinit : ∀i,(∫ω,‖a i ω-e i ω‖^2 ∂ν)≤H^2) (N : ℕ) (i : I) :
    Integrable (fun ω => ‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2) ν ∧
      (∫ω,‖nodes w φ (fun ω j => a j ω) N ω i-e i ω‖^2 ∂ν)≤
        (2*D+(A*K:ℝ≥0)^N*H)^2 := by
  let aLp : I → Lp E 2 ν := fun j => (ha j).toLp (a j)
  let eLp : I → Lp E 2 ν := fun j => (he j).toLp (e j)
  have ha' (j : I) : (aLp j : Ω → E)=ᵐ[ν] a j := (ha j).coeFn_toLp
  have he' (j : I) : (eLp j : Ω → E)=ᵐ[ν] e j := (he j).coeFn_toLp
  have hstep (j : I) : (stepLp w φ hφ aLp eLp j : Ω → E)=ᵐ[ν]
      fun ω => step w φ (fun i => a i ω) (fun i => e i ω) j := by
    filter_upwards [stepLp_ae w φ hφ aLp eLp j,ae_all_iff.mpr ha',ae_all_iff.mpr he'] with ω h1 h2 h3
    simpa only [h2,h3] using h1
  have hdef' (j : I) : dist (stepLp w φ hφ aLp eLp j) (eLp j)≤D := by
    have hh := (lp_rms_eq _ _ (hstep j) (he' j)).2
    have hb := hdef j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=stepLp w φ hφ aLp eLp j) (y:=eLp j)]
  have hinit' : dist aLp eLp≤H := by
    apply (dist_pi_le_iff hH).mpr
    intro j
    have hh := (lp_rms_eq _ _ (ha' j) (he' j)).2
    have hb := hinit j
    rw [hh] at hb
    nlinarith [dist_nonneg (x:=aLp j) (y:=eLp j)]
  have hb := rms_picard_defect w φ hφ aLp eLp hw hq hD hdef' N
  have hrms := lp_rms_eq _ _ (iterateLp_nodes_ae w φ hφ a aLp ha' N i) (he' i)
  refine ⟨hrms.1,?_⟩
  rw [hrms.2]
  apply pow_le_pow_left₀ dist_nonneg _ 2
  exact (dist_le_pi_dist _ _ i).trans (hb.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinit' (show 0≤((A*K:ℝ≥0):ℝ)^N from by positivity))))
end LogConcaveSampling.FinitePicard

end

end

end

end OAI
