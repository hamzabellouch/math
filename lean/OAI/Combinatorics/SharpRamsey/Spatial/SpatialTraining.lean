import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialGeometry
import OAI.Combinatorics.SharpRamsey.Learning.PreparationInvariance

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

lemma scale_B {q N P : ℝ} (hq : 0<q) (hN : 0<N) (hsmall : N^2≤2*q^4)
    (hP : 0≤P) (hscale : 2*exp (6*P)≤q) : exp (3*P)≤q^3/N := by
  have hNq : N≤2*q^2 := by nlinarith [sq_nonneg (N-2*q^2)]
  have hqB : q/2≤q^3/N := by
    apply (le_div_iff₀ hN).mpr
    nlinarith [mul_le_mul_of_nonneg_left hNq hq.le]
  apply (exp_le_exp.mpr (show 3*P≤6*P by linarith)).trans
  exact (show exp (6*P)≤q/2 by linarith).trans hqB

lemma spatial_error {q B L b e X f : ℝ} (hq : 0<q) (hB : 0≤B) (hL : 0≤L)
    (hf : f≤1/25) (hX : X≤50000*B*exp (L/1000))
    (herror : 50000*exp (-(95/100:ℝ)*L)≤exp (-b-e)/800) :
    exp (-L*(1-f))*X≤(q*B*exp (-b-e)/8)/(100*q) := by
  calc
    _ ≤ exp (-L*(1-f))*(50000*B*exp (L/1000)) := mul_le_mul_of_nonneg_left hX (exp_pos _).le
    _ = 50000*B*exp (-L*(1-f)+L/1000) := by rw [exp_add]; ring
    _ ≤ 50000*B*exp (-(95/100:ℝ)*L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by nlinarith [mul_nonneg hL (sub_nonneg.mpr hf)])
    _ ≤ (q*B*exp (-b-e)/8)/(100*q) := by
      have hh := mul_le_mul_of_nonneg_left herror hB
      have he : (q*B*exp (-b-e)/8)/(100*q)=B*exp (-b-e)/800 := by field_simp; ring
      rw [he]
      nlinarith only [hh]

variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialTraining_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialTraining_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialTraining_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem training (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P τ : ℝ) (R p h : ℕ) (L c : ℝ≥0)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) ∧
    exp (3*P)≤(Nat.card K:ℝ)^3/S.card ∧ (c:ℝ)≤1/100 ∧
    E₀.Nonempty ∧ (T.card:ℝ)≤2*E₀.card ∧
    E₀⊆badHyperplanes S plane bs c ∧
    ∀ H∈E₀,mass S c H≤2*τ := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hsp : (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) := by
    apply hsparse.trans
    have hh := mul_le_mul_of_nonneg_right hτsmall (show 0≤(S.card:ℝ)*T.card by positivity)
    calc
      _ ≤ ((1/20:ℝ)*((S.card:ℝ)*T.card))/(Nat.card K:ℝ) :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hh) hq.le
      _ = _ := by ring
  have hsmall : N^2≤2*q^4 := Incidence.sparse_smaller_square (n:=1) hdim S T hST hsp
  have hBbig : exp (3*P)≤q^3/N := scale_B hq hNs hsmall (by linarith [hbud.large])
    (by simpa only [hqexp] using hbud.B)
  have hcsmall : (c:ℝ)≤1/100 := by
    rw [hc]
    apply (div_le_iff₀ hNs).mpr
    have hp : 1≤P := by linarith [hbud.large]
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤100*q by positivity)]
  have htrain : (∑ H∈T,mass S c H)≤τ*T.card := by
    rw [PlanarLearning.sparse_mass,hc]
    have hh := mul_le_mul_of_nonneg_left hsparse (show 0≤q/N by positivity)
    have he : (q/N)*(τ*(S.card:ℝ)*T.card/Nat.card K)=τ*T.card := by
      change (q/N)*(τ*N*T.card/q)=τ*T.card
      field_simp
    exact hh.trans_eq he
  obtain ⟨hE₀,hhalf,hE₀E,hsmallE⟩ := sparse_training S plane bs c T hT τ hτ
    (by linarith) htrain
  exact ⟨hsp,hBbig,hcsmall,hE₀,by linarith only [hhalf],hE₀E,hsmallE⟩

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma training_size {q N t z : ℝ} (hN : 0<N) (hz : 0≤z) (b e : ℝ)
    (hprod : q^4*exp (-b)≤N*t) (hhalf : t≤2*z) :
    q*(q^3/N)*exp (-b-e)/8≤z*exp (-e)/2 := by
  have hTlow : q*(q^3/N)*exp (-b)≤t := by
    have he : q*(q^3/N)*exp (-b)=q^4*exp (-b)/N := by ring
    rw [he]
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hprod
  have he : exp (-b-e)=exp (-b)*exp (-e) := by
    simpa only [sub_eq_add_neg] using exp_add (-b) (-e)
  rw [he]
  have ht : q*(q^3/N)*exp (-b)≤2*z := hTlow.trans hhalf
  have hh := mul_le_mul_of_nonneg_right ht (exp_pos (-e)).le
  nlinarith only [hh,mul_nonneg hz (exp_pos (-e)).le]

end
end SharpLogRamsey.SpatialLearning

end

end OAI
