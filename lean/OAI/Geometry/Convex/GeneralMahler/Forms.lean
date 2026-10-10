import OAI.Geometry.Convex.GeneralMahler.Prim
import OAI.Geometry.Convex.GeneralMahler.Compare
import OAI.Geometry.Convex.GeneralMahler.MatrixDeriv

namespace OAI
/-! Forms on the Hermite coefficients. D and sigma in paper §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
lemma pj_ss (W A B C D:Mat m) :
    Pj W (A-B) (C-D)= Pj W A C-Pj W A D-Pj W B C+Pj W B D := by
  simp_rw [← pJ_eq]
  simp only [_root_.map_sub,_root_.sub_apply]; ring
lemma pJ_smul_left (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W (a•A) C=a*Pj W A C := by simpa using pj_scale a 1 W A C
lemma pJ_smul_right (W:Mat m) (A C:Mat m) (a:ℝ) :
    Pj W A (a•C)=a*Pj W A C := by simpa using pj_scale 1 a W A C

lemma pj_poly_part {f: Rn m→Mat m} (hf:regular f) (W:Mat m) :
    Integrable (fun x=>Pj W (f x) (f x)) (normal m) := by
  simp_rw [← pJ_eq]
  exact ProjField.proj_int W hf hf

namespace ProjField
variable [NeZero m] (q:ProjField m)
def DLMat (l:ℝ→ℝ) (x:Rn m) (i:Fin m) := fderiv ℝ (q.FL.eval (pl l)) x (e i)
def dirF (W:Mat m) (l:ℝ→ℝ) := ∑ i:Fin m,
  Pt W (fun x=>q.DLMat l x i) (fun x=>q.DLMat l x i)
lemma dl_raise {l:ℝ→ℝ} (hl:TestF l) (i:Fin m) (a:MI m) :
    cof (fun x=>q.DLMat l x i) a=sn (a i+1) • cof (q.FL.eval (pl l)) (inc a i) := by
  have hh := pl_test hl
  let f := q.FL.eval (pl l)
  have hi := q.FL.eval_reg hh
  have hf : Differentiable ℝ f := fun x=>(q.hasdl x hh).differentiableAt
  have hv := PLip.fd hf (q.dPoly hh)
  have h := q.LD_reg i hh
  exact coef_raise hi.p hv hf.continuous (ae_of_all _ fun x=>(hf x).hasFDerivAt) i h.p h.meas a

lemma Pt_dir (W:Mat m) {l:ℝ→ℝ} (hl:TestF l) :
    let b := q.FL.eval (pl l)
    HasSum (fun a:MI m=> (deg a:ℝ)* CpPair W b b a) (q.dirF W l) := by
  intro b
  let f := fun (i:Fin m) (a:MI m)=> (a i:ℝ)*CpPair W b b a
  have he (a): (deg a:ℝ)*CpPair W b b a=∑ i,f i a := by
    unfold f deg; rw [← Finset.sum_mul,Nat.cast_sum]
  have hh (i) :
      let c := fun x=>q.DLMat l x i
      HasSum (f i) (Pt W c c) := by
    intro c
    have hi : regular c := q.LD_reg i (pl_test hl)
    have hp := pt_sum (B:=W) hi hi
    have h (a) : CpPair W c c a=f i (inc a i) := by
      unfold CpPair
      rw [show cof c a= _ from q.dl_raise hl i a,pj_scale]
      unfold f CpPair b
      rw [inc_at,← mul_assoc,← pow_two,snsq]
    rw [funext h] at hp
    obtain ⟨he₁,he₂⟩ := inc_sum i (f i) fun a ha=>by simp [ha,f]
    rw [hp.tsum_eq] at he₂
    exact he₂ ▸ (he₁.mpr hp.summable).hasSum
  simp_rw [he]
  exact hasSum_sum fun i _=>hh i

def DD (l:ℝ→ℝ) (a:MI m) := kMode a • cof (q.Hmat (fl l)) a-cof (q.FL.eval (pl l)) a
def Dterm (l:ℝ→ℝ) (a:MI m) := (1+(deg a:ℝ))*Pj q.covMat (q.DD l a) (q.DD l a)
def Dnorm (l:ℝ→ℝ) := ∑' a:MI m,q.Dterm l a

def RR (x:Rn m) := q.Amat x-q.Lmat x
def sigterm (l:ℝ→ℝ) (a:MI m) := Pj q.covMat (cof q.RR a) (q.DD l a)
def sigma (l:ℝ→ℝ) := 2 * ∑' a,q.sigterm l a

lemma H_K_split {l} (hl:TestF l) :
    let f := q.Hmat (fl l)
    let b := q.FL.eval (pl l)
    let W := q.covMat
    HasSum (q.Dterm l) (KP W f f-2*Pt W f b+Pt W b b+q.dirF W l) := by
  intro f b W
  have hf : regular f:= q.regH (fl_test hl)
  have hb : regular b:=q.FL.eval_reg (pl_test hl)
  have h₁ := (K_sum (B:=W) hf hf).hasSum
  have h₂ := pt_sum (B:=W) hf hb
  have h₃ := pt_sum (B:=W) hb hb
  have h₄ := q.Pt_dir W hl
  have he (a:MI m) :
      q.Dterm l a=CpPair W f f a*kMode a-2*CpPair W f b a+
        CpPair W b b a+(deg a:ℝ)*CpPair W b b a := by
    change (1+_)*Pj W (kMode a • cof f a - cof b a) (kMode a • cof f a - cof b a)=_
    simp only [pj_ss,pJ_smul_left,pJ_smul_right]
    rw [pj_sym W (cof b _)]
    unfold CpPair kMode
    have hi : 0 < 1+(deg a:ℝ) := by positivity
    field_simp; ring
  rw [funext he]
  exact (((h₁.sub (h₂.mul_left 2)).add h₃).add h₄)

lemma R_reg : regular q.RR :=
  ⟨q.A_poly.sub q.L_poly,q.A_SM.aestronglyMeasurable.sub q.L_cont.aestronglyMeasurable⟩
lemma sig_split {l:ℝ→ℝ} (hl:TestF l) :
    let f := q.Hmat (fl l)
    let b := q.FL.eval (pl l)
    let W := q.covMat
    HasSum (q.sigterm l) (KP W q.RR f-Pt W q.RR b) := by
  intro f b W
  have hf : regular f:= q.regH (fl_test hl)
  have hb : regular b:=q.FL.eval_reg (pl_test hl)
  have h₁ := (K_sum (B:=W) q.R_reg hf).hasSum
  have h₂ := pt_sum (B:=W) q.R_reg hb
  have he (a:MI m) : q.sigterm l a=CpPair W q.RR f a*kMode a-CpPair W q.RR b a := by
    unfold sigterm DD CpPair
    have hi (A B C:Mat m) : Pj W A (B-C)= Pj W A B-Pj W A C := by
      simp_rw [← pJ_eq]; rw [_root_.map_sub]
    rw [show q.covMat=W from rfl,hi,pJ_smul_right,mul_comm]
  rw [funext he]
  exact h₁.sub h₂

def Jtest (W:Mat m) (l:ℝ→ℝ) :=
  etw W (fun x=> q.Lmat x*q.FL.eval (pl (fun z=>l z^2)) x)-q.dirF W l
end ProjField
end GeneralMahler

end

end OAI
