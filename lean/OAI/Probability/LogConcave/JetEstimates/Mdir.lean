import Mathlib
import OAI.Probability.LogConcave.JetEstimates.MixedJetAdd

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι]

lemma jet_dir {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (v : κ → E) (l : List κ) (w : E) : jet v l (dir w f)=dir w (jet v l f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [jet,ih]
    exact dir_dir (smooth_jet hf v l) (v i) w

def mdir (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ) (f : E → ℝ) : E → ℝ :=
  fun p => dir w f p-r*∑ i, M i p*dir (b i) f p

lemma smooth_mdir (w : E) (b : ι → E) (r : ℝ) {M : ι → E → ℝ}
    (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i)) {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) :
    ContDiff ℝ (⊤:ℕ∞) (mdir w b r M f) :=
  (smooth_dir hf w).sub (contDiff_const.mul (ContDiff.sum fun i _ => (hM i).mul (smooth_dir hf _)))

lemma mdir_sum {N : Type*} (s : Finset N) (w : E) (b : ι → E) (r : ℝ)
    (M : ι → E → ℝ) {f : N → E → ℝ} (hf : ∀n∈s,Differentiable ℝ (f n)) :
    mdir w b r M (fun p => ∑n∈s,f n p)=fun p => ∑n∈s,mdir w b r M (f n) p := by
  unfold mdir
  rw [dir_sum s hf]
  simp_rw [dir_sum s hf]
  funext p
  simp only [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mdir_add (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    mdir w b r M (fun p => f p+g p)=fun p => mdir w b r M f p+mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_add hf hg]
  funext p
  simp only [mul_add,Finset.sum_add_distrib]
  ring

lemma mdir_const_mul (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f : E → ℝ} (hf : Differentiable ℝ f) (c : ℝ) :
    mdir w b r M (fun p => c*f p)=fun p => c*mdir w b r M f p := by
  unfold mdir
  simp_rw [dir_const_mul hf]
  funext p
  have he : (∑i,M i p*(c*dir (b i) f p))=c*∑i,M i p*dir (b i) f p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

lemma mdir_mul (w : E) (b : ι → E) (r : ℝ) (M : ι → E → ℝ)
    {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    mdir w b r M (fun p => f p*g p)=fun p =>
      mdir w b r M f p*g p+f p*mdir w b r M g p := by
  unfold mdir
  simp_rw [dir_mul hf hg]
  funext p
  have he : (∑i,M i p*(dir (b i) f p*g p+f p*dir (b i) g p))=
      (∑i,M i p*dir (b i) f p)*g p+f p*∑i,M i p*dir (b i) g p := by
    rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem mdir_jet [DecidableEq κ] (w : E) (b : ι → E) (r : ℝ)
    {M : ι → E → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f)
    (v : κ → E) (l : List κ) (hl : l.Nodup) :
    mdir w b r M (jet v l f)=fun p => jet v l (mdir w b r M f) p+
      r*∑s∈l.toFinset.powerset.erase ∅,∑i,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
  have hm : ContDiff ℝ (⊤:ℕ∞) (fun p => ∑i,M i p*dir (b i) f p) :=
    ContDiff.sum fun i _ => (hM i).mul (smooth_dir hf _)
  have he : jet v l (mdir w b r M f)=fun p => dir w (jet v l f) p-
      r*∑i,∑s∈l.toFinset.powerset,
        jet v (l.filter (fun j => j∈s)) (M i) p*
          dir (b i) (jet v (l.filter (fun j => j∉s)) f) p := by
    unfold mdir
    rw [jet_sub (smooth_dir hf w) (contDiff_const.mul hm),jet_const_mul hm,
      jet_dir hf,jet_sum Finset.univ (fun i _ => (hM i).mul (smooth_dir hf _))]
    simp_rw [jet_mul (hM _) (smooth_dir hf _) v l hl,jet_dir hf]
  rw [he]
  funext p
  dsimp only
  rw [Finset.sum_comm]
  rw [←Finset.add_sum_erase _ _ (by simp : (∅:Finset κ)∈l.toFinset.powerset)]
  simp only [Finset.notMem_empty,decide_false,List.filter_false,not_false_eq_true,decide_true,
    List.filter_true,jet]
  unfold mdir
  ring

end LogConcaveSampling.JetCalculus

end

end

section

noncomputable section
namespace LogConcaveSampling.JetCalculus
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma mdir_dir (w : E) (b : ι → E) (r : ℝ)
    {M : ι → E → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : E) :
    mdir w b r M (dir v f)=fun p => dir v (mdir w b r M f) p+
      r*∑i,dir v (M i) p*dir (b i) f p := by
  have ht := mdir_jet w b r hM hf (fun _ : Unit => v) [()] (by simp)
  have hp : ({()} : Finset Unit).powerset.erase ∅ = {{()}} := by decide
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] at ht
  rw [hp] at ht
  simpa [jet] using ht

def cadj (v : E) (s f : E → ℝ) : E → ℝ := fun p => -dir v f p+s p*f p

def gadj (b : ι → E) (s V : ι → E → ℝ) : E → ℝ := fun p => ∑i,cadj (b i) (s i) (V i) p

lemma smooth_cadj (v : E) {s f : E → ℝ} (hs : ContDiff ℝ (⊤:ℕ∞) s)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) : ContDiff ℝ (⊤:ℕ∞) (cadj v s f) :=
  (smooth_dir hf v).neg.add (hs.mul hf)

lemma gadj_sum {N : Type*} (a : Finset N) (b : ι → E) (s : ι → E → ℝ)
    {V : N → ι → E → ℝ} (hV : ∀n∈a,∀i,Differentiable ℝ (V n i)) :
    gadj b s (fun i p => ∑n∈a,V n i p)=fun p => ∑n∈a,gadj b s (V n) p := by
  unfold gadj cadj
  simp_rw [dir_sum a (fun n hn => hV n hn _)]
  funext p
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib]

lemma gadj_mul (b : ι → E) (s : ι → E → ℝ) {V : ι → E → ℝ}
    (hV : ∀i,Differentiable ℝ (V i)) {f : E → ℝ} (hf : Differentiable ℝ f) :
    gadj b s (fun i p => V i p*f p)=fun p => gadj b s V p*f p-∑i,V i p*dir (b i) f p := by
  unfold gadj cadj
  simp_rw [dir_mul (hV _) hf]
  funext p
  rw [Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mdir_cadj (w : E) (b : ι → E) (r : ℝ)
    {M s : ι → E → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    (hs : ∀i,ContDiff ℝ (⊤:ℕ∞) (s i))
    {f : E → ℝ} (hf : ContDiff ℝ (⊤:ℕ∞) f) (i : ι)
    (hsi : mdir w b r M (s i)=fun p => r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (cadj (b i) (s i) f)=fun p =>
      cadj (b i) (s i) (mdir w b r M f) p+
        r*gadj b s (fun k p => dir (b i) (M k) p*f p) p := by
  have hdf := smooth_dir hf (b i)
  have hMi (k : ι) := smooth_dir (hM k) (b i)
  have he : cadj (b i) (s i) f=fun p => (-1)*dir (b i) f p+s i p*f p := by
    funext p; simp [cadj]
  rw [he,mdir_add w b r M ((contDiff_const.mul hdf).differentiable (by simp))
    (((hs i).mul hf).differentiable (by simp))]
  rw [mdir_const_mul w b r M (hdf.differentiable (by simp)),
      mdir_mul w b r M ((hs i).differentiable (by simp)) (hf.differentiable (by simp)),
      mdir_dir w b r hM hf,hsi]
  rw [gadj_mul b s (fun k => (hMi k).differentiable (by simp)) (hf.differentiable (by simp))]
  funext p
  simp only [cadj]
  ring

theorem mdir_gadj (w : E) (b : ι → E) (r : ℝ)
    {M s V : ι → E → ℝ} (hM : ∀i,ContDiff ℝ (⊤:ℕ∞) (M i))
    (hs : ∀i,ContDiff ℝ (⊤:ℕ∞) (s i)) (hV : ∀i,ContDiff ℝ (⊤:ℕ∞) (V i))
    (hscore : ∀i,mdir w b r M (s i)=fun p => r*gadj b s (fun k => dir (b i) (M k)) p) :
    mdir w b r M (gadj b s V)=fun p =>
      gadj b s (fun i => mdir w b r M (V i)) p+
      r*gadj b s (fun k p => ∑i,dir (b i) (M k) p*V i p) p := by
  change mdir w b r M (fun p => ∑i,cadj (b i) (s i) (V i) p)=_
  rw [mdir_sum Finset.univ w b r M (fun i _ =>
    (smooth_cadj (b i) (hs i) (hV i)).differentiable (by simp))]
  simp_rw [mdir_cadj w b r hM hs (hV _) _ (hscore _)]
  rw [gadj_sum Finset.univ b s (fun i _ k =>
    ((smooth_dir (hM k) (b i)).mul (hV i)).differentiable (by simp))]
  funext p
  simp only [Finset.sum_add_distrib,Finset.mul_sum,gadj]

end LogConcaveSampling.JetCalculus

end

end

end

end OAI
