import Mathlib
import OAI.Probability.SKValue.Gaussian.EvenEvolution
import OAI.Probability.SKValue.Evolution.BurgersJets
import OAI.Probability.SKValue.Evolution.HeatConvexity

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SKValue

structure BackwardBurgers where
  jet : ℕ → ℝ → ℝ → ℝ
  continuous : ∀ n, Continuous (fun p : ℝ×ℝ ↦ jet n p.1 p.2)
  bound : ∀ n, ∃ C : ℝ,0≤C ∧ ∀ t x,|jet n t x|≤C
  space : ∀ n t x, HasDerivAt (jet n t) (jet (n+1) t x) x
  time0 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 0 s x)
    ((1/2:ℝ)*jet 2 t x+jet 0 t x*jet 1 t x) t
  time1 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 1 s x)
    ((1/2:ℝ)*jet 3 t x+(jet 1 t x)^2+jet 0 t x*jet 2 t x) t
  time2 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 2 s x)
    ((1/2:ℝ)*jet 4 t x+3*jet 1 t x*jet 2 t x+jet 0 t x*jet 3 t x) t
  time3 : ∀ t,0<t → ∀ x, HasDerivAt (fun s ↦ jet 3 s x)
    ((1/2:ℝ)*jet 5 t x+3*(jet 2 t x)^2+4*jet 1 t x*jet 3 t x+jet 0 t x*jet 4 t x) t
  zero0 : ∀ t, jet 0 t 0=0
  zero2 : ∀ t, jet 2 t 0=0
  positive : ∀ t x,0<x → 0<jet 0 t x
  slope_nonneg : ∀ t x,0≤jet 1 t x

lemma even_third_deriv_zero {f : ℝ → ℝ} (hf : ∀ x,f (-x)=f x) :
    iteratedDeriv 2 (deriv f) 0=0 := by
  have h := iteratedDeriv_comp_neg 3 f (0:ℝ)
  have he : (fun x ↦ f (-x))=f := funext hf
  rw [he] at h
  norm_num only [neg_zero,smul_eq_mul] at h
  have hz : iteratedDeriv 3 f 0=0 := by linarith
  simpa only [iteratedDeriv_succ'] using hz

noncomputable def SmoothTerminal.backwardBurgers {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (heven : ∀ x,ψ (-x)=ψ x) (hcurv : ∀ x,0<deriv (deriv ψ) x)
    {c : ℝ} (hc : 0<c) : BackwardBurgers where
  jet := scaledHeatJet c ψ
  continuous := scaledHeatJet_continuous hψ hc.le
  bound := scaledHeatJet_bound hψ hc
  space := scaledHeatJet_space hψ hc.le
  time0 := fun _ ht x ↦ scaledHeatJet_time0 hψ hc ht x
  time1 := fun _ ht x ↦ scaledHeatJet_time1 hψ hc ht x
  time2 := fun _ ht x ↦ scaledHeatJet_time2 hψ hc ht x
  time3 := fun _ ht x ↦ scaledHeatJet_time3 hψ hc ht x
  zero0 := by
    intro t
    simp only [scaledHeatJet,iteratedDeriv_zero,deriv_even_zero (coleHopf_even heven c t),mul_zero]
  zero2 := by
    intro t
    simp only [scaledHeatJet,even_third_deriv_zero (coleHopf_even heven c t),mul_zero]
  positive := by
    intro t x hx
    have hp := hψ.coleHopf_curvature_pos hcurv hc t
    have hm := strictMono_of_deriv_pos hp
    have hh := hm hx
    rw [deriv_even_zero (coleHopf_even heven c t)] at hh
    exact mul_pos hc hh
  slope_nonneg := by
    intro t x
    simpa only [scaledHeatJet,iteratedDeriv_one] using (mul_pos hc (hψ.coleHopf_curvature_pos hcurv hc t x)).le

namespace BackwardBurgers
variable (F : BackwardBurgers)

noncomputable def k (t x : ℝ) := F.jet 2 t x+2*F.jet 0 t x*F.jet 1 t x
noncomputable def kx (t x : ℝ) := F.jet 3 t x+2*(F.jet 1 t x)^2+2*F.jet 0 t x*F.jet 2 t x
noncomputable def kxx (t x : ℝ) := F.jet 4 t x+6*F.jet 1 t x*F.jet 2 t x+2*F.jet 0 t x*F.jet 3 t x
noncomputable def kt (t x : ℝ) := (1/2:ℝ)*F.kxx t x+F.jet 0 t x*F.kx t x+F.jet 1 t x*F.k t x
noncomputable def n (t x : ℝ) := F.jet 0 t x*F.jet 3 t x-F.jet 1 t x*F.jet 2 t x+2*(F.jet 0 t x)^2*F.jet 2 t x
noncomputable def nx (t x : ℝ) := F.jet 0 t x*F.jet 4 t x-(F.jet 2 t x)^2+
  4*F.jet 0 t x*F.jet 1 t x*F.jet 2 t x+2*(F.jet 0 t x)^2*F.jet 3 t x
noncomputable def nxx (t x : ℝ) := F.jet 0 t x*F.jet 5 t x+F.jet 1 t x*F.jet 4 t x-
  2*F.jet 2 t x*F.jet 3 t x+4*(F.jet 1 t x)^2*F.jet 2 t x+
  4*F.jet 0 t x*(F.jet 2 t x)^2+8*F.jet 0 t x*F.jet 1 t x*F.jet 3 t x+
  2*(F.jet 0 t x)^2*F.jet 4 t x
noncomputable def nt (t x : ℝ) := (1/2:ℝ)*F.nxx t x+
  (F.jet 0 t x-F.jet 1 t x/F.jet 0 t x)*F.nx t x+
  (F.k t x/F.jet 0 t x)*F.n t x+F.jet 0 t x*F.jet 2 t x*F.k t x

lemma k_space (t x : ℝ) : HasDerivAt (F.k t) (F.kx t x) x := by
  have hd := (F.space 2 t x).add (((F.space 0 t x).const_mul 2).mul (F.space 1 t x))
  convert! hd using 1
  dsimp [k,kx]
  ring
lemma kx_space (t x : ℝ) : HasDerivAt (F.kx t) (F.kxx t x) x := by
  have hd := ((F.space 3 t x).add (((F.space 1 t x).pow 2).const_mul 2)).add
    (((F.space 0 t x).const_mul 2).mul (F.space 2 t x))
  convert! hd using 1
  dsimp [kx,kxx]
  ring
lemma k_time {t : ℝ} (ht : 0<t) (x : ℝ) : HasDerivAt (F.k · x) (F.kt t x) t := by
  have hd := (F.time2 t ht x).add (((F.time0 t ht x).const_mul 2).mul (F.time1 t ht x))
  convert! hd using 1
  dsimp [k,kt,kx,kxx]
  ring
lemma n_space (t x : ℝ) : HasDerivAt (F.n t) (F.nx t x) x := by
  have hd := (((F.space 0 t x).mul (F.space 3 t x)).sub
    ((F.space 1 t x).mul (F.space 2 t x))).add
    ((((F.space 0 t x).pow 2).const_mul 2).mul (F.space 2 t x))
  convert! hd using 1
  dsimp [n,nx]
  ring
lemma nx_space (t x : ℝ) : HasDerivAt (F.nx t) (F.nxx t x) x := by
  have hd := ((((F.space 0 t x).mul (F.space 4 t x)).sub ((F.space 2 t x).pow 2)).add
    ((((F.space 0 t x).const_mul 4).mul (F.space 1 t x)).mul (F.space 2 t x))).add
    ((((F.space 0 t x).pow 2).const_mul 2).mul (F.space 3 t x))
  convert! hd using 1
  dsimp [nx,nxx]
  ring
lemma n_time {t x : ℝ} (ht : 0<t) (hx : 0<x) : HasDerivAt (F.n · x) (F.nt t x) t := by
  have hd := (((F.time0 t ht x).mul (F.time3 t ht x)).sub
    ((F.time1 t ht x).mul (F.time2 t ht x))).add
    ((((F.time0 t ht x).pow 2).const_mul 2).mul (F.time2 t ht x))
  convert! hd using 1
  dsimp [n,nt,nx,nxx,k]
  field_simp [(F.positive t x hx).ne']
  ring

lemma k_continuous : Continuous (fun p : ℝ×ℝ ↦ F.k p.1 p.2) :=
  (F.continuous 2).add ((continuous_const.mul (F.continuous 0)).mul (F.continuous 1))
lemma n_continuous : Continuous (fun p : ℝ×ℝ ↦ F.n p.1 p.2) :=
  (((F.continuous 0).mul (F.continuous 3)).sub ((F.continuous 1).mul (F.continuous 2))).add
    ((continuous_const.mul ((F.continuous 0).pow 2)).mul (F.continuous 2))
lemma k_bound : ∃ C : ℝ,0≤C ∧ ∀ t x,|F.k t x|≤C := by
  let e : JetExpr := .add (.coord 2) (.mul (.mul (.const 2) (.coord 0)) (.coord 1))
  have hh : ∀ j,∃ C : ℝ,0≤C ∧ ∀ p : ℝ×ℝ,|F.jet j p.1 p.2|≤C := by
    intro j; obtain ⟨C,hC,h⟩ := F.bound j; exact ⟨C,hC,fun p ↦ h p.1 p.2⟩
  obtain ⟨C,hC,h⟩ := JetExpr.uniform_bound hh e
  exact ⟨C,hC,fun t x ↦ h (t,x)⟩
lemma n_bound : ∃ C : ℝ,0≤C ∧ ∀ t x,|F.n t x|≤C := by
  let e : JetExpr := .add (.add (.mul (.coord 0) (.coord 3))
    (.mul (.const (-1)) (.mul (.coord 1) (.coord 2))))
    (.mul (.mul (.const 2) (.mul (.coord 0) (.coord 0))) (.coord 2))
  have hh : ∀ j,∃ C : ℝ,0≤C ∧ ∀ p : ℝ×ℝ,|F.jet j p.1 p.2|≤C := by
    intro j; obtain ⟨C,hC,h⟩ := F.bound j; exact ⟨C,hC,fun p ↦ h p.1 p.2⟩
  obtain ⟨C,hC,h⟩ := JetExpr.uniform_bound hh e
  refine ⟨C,hC,fun t x ↦ ?_⟩
  convert! h (t,x) using 1
  congr 1
  dsimp [n,e,JetExpr.eval]
  ring

@[simp] lemma k_zero (t : ℝ) : F.k t 0=0 := by simp [k,F.zero2,F.zero0]
@[simp] lemma n_zero (t : ℝ) : F.n t 0=0 := by simp [n,F.zero2,F.zero0]

end BackwardBurgers
end SKValue

end

end OAI
