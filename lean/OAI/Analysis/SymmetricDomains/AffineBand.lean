import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

namespace SemialgebraicOn
variable {ι κ δ : Type*} {B : Set (ι → ℝ)} {f g : (ι → ℝ) → (κ → ℝ)}
lemma reindex [Finite κ] [Finite δ] (hf : SemialgebraicOn B f) (r : δ → κ) :
    SemialgebraicOn B (fun x j => f x (r j)) := by
  have hp := (polynomial (B := (univ : Set (κ → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (r j))).comp hf (fun _ _ => mem_univ _)
  simpa only [Function.comp_def,MvPolynomial.eval_X] using hp

lemma add [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x + g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)

lemma mul [Finite κ] (hf : SemialgebraicOn B f) (hg : SemialgebraicOn B g) :
    SemialgebraicOn B (fun x => f x * g x) := by
  have hp := (polynomial (B := (univ : Set ((κ ⊕ κ) → ℝ))) PolynomialSignSet.univ
    (fun j => MvPolynomial.X (Sum.inl j) * MvPolynomial.X (Sum.inr j))).comp
      (hf.pair hg) (fun _ _ => mem_univ _)
  exact hp.congr (fun x _ => by ext j; simp)

lemma finCons {n : ℕ} {a : (ι → ℝ) → (Fin 1 → ℝ)} {f : (ι → ℝ) → (Fin n → ℝ)}
    (ha : SemialgebraicOn B a) (hf : SemialgebraicOn B f) :
    SemialgebraicOn B (fun x => Fin.cons (a x 0) (f x)) := by
  apply ((ha.pair hf).reindex (Fin.cases (Sum.inl 0) Sum.inr)).congr
  intro x _
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
end SemialgebraicOn

namespace NashPatch

noncomputable def graph {n : ℕ} (p : NashPatch n)
    (a : (Fin p.dim → ℝ) → (Fin 1 → ℝ)) (hs : SemialgebraicOn p.domain a)
    (ha : AnalyticOnNhd ℝ a p.domain) : NashPatch (n+1) where
  dim := p.dim
  domain := p.domain
  isOpen_domain := p.isOpen_domain
  isConnected_domain := p.isConnected_domain
  semialgebraic_domain := p.semialgebraic_domain
  toFun := fun x => Fin.cons (a x 0) (p.toFun x)
  semialgebraic_toFun := hs.finCons p.semialgebraic_toFun
  analytic_toFun x hx := by
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (analyticAt_pi_iff.mp (ha x hx)) 0
    · exact (analyticAt_pi_iff.mp (p.analytic_toFun x hx)) j
  injective_fderiv x hx := by
    have hd := ((analyticAt_pi_iff.mp (ha x hx) 0).differentiableAt.hasFDerivAt).finCons (F' := fun _ : Fin (n+1) => ℝ)
      (p.analytic_toFun x hx).differentiableAt.hasFDerivAt
    rw [hd.fderiv]
    intro u v huv
    apply p.injective_fderiv x hx
    exact congrArg Fin.tail huv

def cylinderDomain {d : ℕ} (B : Set (Fin d → ℝ)) (I : Set ℝ) : Set (Fin (d+1) → ℝ) :=
  {x | Fin.tail x ∈ B ∧ x 0 ∈ I}

lemma cylinderDomain_open {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) : IsOpen (cylinderDomain B I) :=
  (hB.preimage (by fun_prop)).inter (hI.preimage (continuous_apply 0))

lemma cylinderDomain_connected {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : IsConnected B) (hI : IsConnected I) : IsConnected (cylinderDomain B I) := by
  have he : (fun x : ℝ × (Fin d → ℝ) => Fin.cons x.1 x.2) '' (I ×ˢ B) = cylinderDomain B I := by
    ext x
    constructor
    · rintro ⟨⟨t,y⟩,⟨ht,hy⟩,rfl⟩
      exact ⟨hy,ht⟩
    · rintro ⟨hx,ht⟩
      exact ⟨(x 0,Fin.tail x),⟨ht,hx⟩,Fin.cons_self_tail x⟩
  rw [← he]
  exact (hI.prod hB).image _ (by fun_prop)

lemma cylinderDomain_semialgebraic {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : PolynomialSignSet id B) (hI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    PolynomialSignSet id (cylinderDomain B I) := by
  exact (hB.coordinate_preimage Fin.tail Fin.succ (d := id) (by intro x i; rfl)).inter
    (hI.coordinate_preimage (fun x => x 0) (fun _ => 0) (d := id) (by intro x i; rfl))

lemma semialgebraic_tail {d : ℕ} {B : Set (Fin d → ℝ)} {I : Set ℝ}
    (hB : PolynomialSignSet id B) (hI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I) :
    SemialgebraicOn (cylinderDomain B I) (@Fin.tail d (fun _ => ℝ)) := by
  exact (SemialgebraicOn.polynomial
    (cylinderDomain_semialgebraic hB hI) (fun i : Fin d => MvPolynomial.X i.succ)).congr
    (fun x _ => by ext i; simp [Fin.tail])

noncomputable def affineBand {n : ℕ} (p : NashPatch n) (I : Set ℝ)
    (hI : IsOpen I) (hcI : IsConnected I)
    (hsI : PolynomialSignSet (fun t : ℝ => fun _ : Fin 1 => t) I)
    (a b : (Fin p.dim → ℝ) → (Fin 1 → ℝ))
    (hsa : SemialgebraicOn p.domain a) (hsb : SemialgebraicOn p.domain b)
    (haa : AnalyticOnNhd ℝ a p.domain) (hab : AnalyticOnNhd ℝ b p.domain)
    (hb : ∀ x ∈ p.domain, b x 0 ≠ 0) : NashPatch (n+1) where
  dim := p.dim+1
  domain := cylinderDomain p.domain I
  isOpen_domain := cylinderDomain_open p.isOpen_domain hI
  isConnected_domain := cylinderDomain_connected p.isConnected_domain hcI
  semialgebraic_domain := cylinderDomain_semialgebraic p.semialgebraic_domain hsI
  toFun := fun x => Fin.cons (a (Fin.tail x) 0 + b (Fin.tail x) 0 * x 0) (p.toFun (Fin.tail x))
  semialgebraic_toFun := by
    have ht := semialgebraic_tail p.semialgebraic_domain hsI
    have ha := hsa.comp ht (fun _ hx => hx.1)
    have hb := hsb.comp ht (fun _ hx => hx.1)
    have hv : SemialgebraicOn (cylinderDomain p.domain I) (fun x => fun _ : Fin 1 => x 0) := by
      simpa only [MvPolynomial.eval_X] using SemialgebraicOn.polynomial
        (cylinderDomain_semialgebraic p.semialgebraic_domain hsI) (fun _ : Fin 1 => MvPolynomial.X 0)
    exact (ha.add (hb.mul hv)).finCons (p.semialgebraic_toFun.comp ht (fun _ hx => hx.1))
  analytic_toFun x hx := by
    have ht : AnalyticAt ℝ (@Fin.tail p.dim (fun _ => ℝ)) x :=
      (Pi.compRightL ℝ (fun _ : Fin (p.dim+1) => ℝ) Fin.succ).analyticAt x
    have ha := (analyticAt_pi_iff.mp (haa _ hx.1) 0).comp ht
    have hb := (analyticAt_pi_iff.mp (hab _ hx.1) 0).comp ht
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha.add (hb.mul ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (p.dim+1) => ℝ) 0).analyticAt x))
    · exact (analyticAt_pi_iff.mp (p.analytic_toFun _ hx.1) j).comp ht
  injective_fderiv x hx := by
    let T : (Fin (p.dim+1) → ℝ) →L[ℝ] (Fin p.dim → ℝ) := Pi.compRightL ℝ (fun _ => ℝ) Fin.succ
    let Z : (Fin (p.dim+1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    have ht : HasFDerivAt (@Fin.tail p.dim (fun _ => ℝ)) T x := T.hasFDerivAt
    have hz : HasFDerivAt (fun x : Fin (p.dim+1) → ℝ => x 0) Z x := Z.hasFDerivAt
    have ha := ((analyticAt_pi_iff.mp (haa _ hx.1) 0).differentiableAt.hasFDerivAt).comp x ht
    have hb' := ((analyticAt_pi_iff.mp (hab _ hx.1) 0).differentiableAt.hasFDerivAt).comp x ht
    have hp := (p.analytic_toFun _ hx.1).differentiableAt.hasFDerivAt.comp x ht
    have hd := (ha.add (hb'.mul hz)).finCons (F' := fun _ : Fin (n+1) => ℝ) hp
    simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply] at hd
    rw [hd.fderiv]
    intro u v huv
    have htail : Fin.tail u = Fin.tail v := by
      apply p.injective_fderiv _ hx.1
      exact congrArg Fin.tail huv
    have hzero := congrFun huv 0
    change fderiv ℝ (fun y => a y 0) (Fin.tail x) (T u) +
      (b (Fin.tail x) 0 * Z u + x 0 * fderiv ℝ (fun y => b y 0) (Fin.tail x) (T u)) =
      fderiv ℝ (fun y => a y 0) (Fin.tail x) (T v) +
      (b (Fin.tail x) 0 * Z v + x 0 * fderiv ℝ (fun y => b y 0) (Fin.tail x) (T v)) at hzero
    change T u = T v at htail
    rw [htail] at hzero
    dsimp [Z] at hzero
    have hzuv : u 0 = v 0 := mul_left_cancel₀ (hb _ hx.1) (by linarith [hzero])
    funext i
    exact Fin.cases hzuv (fun j => congrFun htail j) i

end NashPatch
end Release061

end

end OAI
