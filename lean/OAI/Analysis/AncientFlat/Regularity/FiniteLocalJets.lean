import OAI.Analysis.AncientFlat.Regularity.ParabolicInterpolation
import OAI.Analysis.AncientFlat.Regularity.HolderProducts
import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicInterior
open ParabolicInterpolation ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma finite_jet_of_fourth_local (α K U H R : ℝ) (hα : 0<α) (hα1 : α<1)
    (hK : 0≤K) (hU : 0≤U) (hH : 0≤H) (I : Set ℝ) (hI : OrdConnected I)
    (a : V × ℝ → ℝ) (b : V × ℝ → ℂ) (u ut f : ℝ → V → ℂ)
    (ha : HolderBound α {p | ‖p.1‖<R+12 ∧ p.2∈I} a K) (hb : HolderBound α {p | ‖p.1‖<R+12 ∧ p.2∈I} b K)
    (hf : HolderBound α {p | ‖p.1‖<R+12 ∧ p.2∈I} (fun p => f p.2 p.1) K)
    (hu : ∀ t∈I, ∀ x, ‖x‖<R+12 → ‖u t x‖≤U)
    (h4 : HolderBound α {p | ‖p.1‖<R+12 ∧ p.2∈I} (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) H)
    (hs : ∀ t∈I, ContDiff ℝ 4 (u t))
    (hd : ∀ t∈I, ∀ x, HasDerivAt (fun t => u t x) (ut t x) t)
    (he : ∀ t∈I, ∀ x, ut t x+(a (x,t) : ℂ)*Δ (Δ (u t)) x+b (x,t)*u t x=f t x) :
    ∃ M : ℝ, 0≤M ∧ JetBound α {p | ‖p.1‖<R ∧ p.2∈I} u ut M := by
  let T : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ := traceFour
  let B := H+K+K*‖T‖*H+K*U
  have hB : 0≤B := by dsimp [B]; positivity
  have hut (t) (ht : t∈I) (x : V) (hx : ‖x‖<R+12) : ‖ut t x‖≤B := by
    have heq : ut t x=f t x-(a (x,t) : ℂ)*T (iteratedFDeriv ℝ 4 (u t) x)-b (x,t)*u t x := by
      have hh := he t ht x
      rw [bilaplacian_eq_traceFour _ (hs t ht)] at hh
      dsimp [T]
      linear_combination hh
    rw [heq]
    have htrace : ‖T (iteratedFDeriv ℝ 4 (u t) x)‖≤‖T‖*H :=
      (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h4.1 (x,t) ⟨hx,ht⟩) (norm_nonneg T))
    have hprod : ‖(a (x,t) : ℂ)*T (iteratedFDeriv ℝ 4 (u t) x)‖≤K*(‖T‖*H) := by
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul (ha.1 (x,t) ⟨hx,ht⟩) htrace (norm_nonneg _) hK
    have hprod' : ‖b (x,t)*u t x‖≤K*U := by
      rw [norm_mul]; exact mul_le_mul (hb.1 (x,t) ⟨hx,ht⟩) (hu t ht x hx) (norm_nonneg _) hK
    calc
      _ ≤ ‖f t x‖+‖(a (x,t) : ℂ)*T (iteratedFDeriv ℝ 4 (u t) x)‖+‖b (x,t)*u t x‖ :=
        (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
      _ ≤ K+K*(‖T‖*H)+K*U := add_le_add (add_le_add (hf.1 (x,t) ⟨hx,ht⟩) hprod) hprod'
      _ ≤ B := by dsimp [B]; nlinarith
  let D := 110*(U+B)
  have hD : 0≤D := by dsimp [D]; positivity
  have Hlow (n : ℕ) (hn : n≤3) : HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈I}
      (fun p => iteratedFDeriv ℝ n (u p.2) p.1) D := by
    have hh := lower_parabolic_bound n hn u ut I hI R (R+12) 1 U B α zero_lt_one le_rfl
      (by ring_nf; exact le_rfl) hU hB hα.le hα1.le hs (fun t ht x _ => hd t ht x)
      (fun t ht x hx => hut t ht x hx) (fun t ht x hx => hu t ht x hx)
      (fun t ht x hx => (h4.1 (x,t) ⟨hx,ht⟩).trans (by dsimp [B]; nlinarith [mul_nonneg (mul_nonneg hK (norm_nonneg T)) hH,mul_nonneg hK hU]))
    simpa only [one_pow,Real.one_rpow,div_one,one_mul,D] using hh
  have hh0 := Hlow 0 (by norm_num)
  have hv : HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈I} (fun p => u p.2 p.1) D := by
    constructor
    · intro p hp; simpa only [norm_iteratedFDeriv_zero] using hh0.1 p hp
    · intro p hp q hq
      have hh := hh0.2 p hp q hq
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] using hh
  have hm : {p : V × ℝ | ‖p.1‖<R ∧ p.2∈I}⊆{p : V × ℝ | ‖p.1‖<R+12 ∧ p.2∈I} := fun p hp => ⟨by linarith [hp.1],hp.2⟩
  have htrace := (h4.restrict hm).clm T
  have hprod := (ha.restrict hm).smul htrace hK (mul_nonneg (norm_nonneg T) hH)
  have hprod' := (hb.restrict hm).mul hv hK hD
  have htime := ((hf.restrict hm).add hprod.neg).add hprod'.neg
  let J := K+2*K*(‖T‖*H)+2*K*D
  have hJ : 0≤J := by dsimp [J]; positivity
  refine ⟨D+H+J,by positivity,?_,?_⟩
  · intro n hn
    by_cases hn' : n≤3
    · exact (Hlow n hn').mono (by linarith)
    · have hn4 : n=4 := by omega
      subst n
      exact (h4.restrict hm).mono (by linarith)
  · have hh : HolderBound α {p : V × ℝ | ‖p.1‖<R ∧ p.2∈I} (fun p => ut p.2 p.1) J := by
      constructor
      · intro p hp
        have heq : ut p.2 p.1=(f p.2 p.1+-a p • T (iteratedFDeriv ℝ 4 (u p.2) p.1))+-b p*u p.2 p.1 := by
          have hh := he p.2 hp.2 p.1
          rw [bilaplacian_eq_traceFour _ (hs p.2 hp.2)] at hh
          simp only [Complex.real_smul,Complex.ofReal_neg,neg_mul]
          dsimp [T]; linear_combination hh
        dsimp only
        rw [heq]
        simpa only [neg_smul,neg_mul,J] using htime.1 p hp
      · intro p hp q hq
        have heq (p : V × ℝ) (hp : p∈{p : V × ℝ | ‖p.1‖<R ∧ p.2∈I}) :
            ut p.2 p.1=(f p.2 p.1+-(a p • T (iteratedFDeriv ℝ 4 (u p.2) p.1)))+-(b p*u p.2 p.1) := by
          have hh := he p.2 hp.2 p.1
          rw [bilaplacian_eq_traceFour _ (hs p.2 hp.2)] at hh
          simp only [Complex.real_smul]
          dsimp [T]; linear_combination hh
        dsimp only
        rw [heq p hp,heq q hq]
        exact htime.2 p hp q hq
    exact hh.mono (by linarith)
end ParabolicInterior

end

end OAI
