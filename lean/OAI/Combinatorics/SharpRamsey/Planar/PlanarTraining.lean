import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarGeometry

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarTraining_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarTraining_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarTraining_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarTraining_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem training (hdim : Module.finrank K V=3)
    (S : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S.card≤T.card)
    (σ P τ : ℝ) (R p h : ℕ) (L c : ℝ≥0)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R p h) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card) :
    let E₀ := T.filter (fun H => mass S c H≤2*τ)
    (Incidence.incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K) ∧
    exp (3*P)≤(Nat.card K:ℝ)^2/S.card ∧ (c:ℝ)≤1/100 ∧
    E₀.Nonempty ∧ (T.card:ℝ)≤2*E₀.card ∧
    E₀⊆badHyperplanes S (fun _ : Unit => ∅) [] c ∧
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
  have hsmall : N^2≤2*q^3 := Incidence.sparse_smaller_square (n:=0) hdim S T hST hsp
  have hBbig : exp (3*P)≤q^2/N := scale_B hq hNs hsmall (by simpa only [hqexp] using hbud.B)
  have hcsmall : (c:ℝ)≤1/100 := by
    rw [hc]
    apply (div_le_iff₀ hNs).mpr
    have hp : 1≤P := by linarith [hbud.large]
    nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤100*q by positivity)]
  have htrain : (∑ H∈T,mass S c H)≤τ*T.card := by
    rw [sparse_mass,hc]
    have hh := mul_le_mul_of_nonneg_left hsparse (show 0≤q/N by positivity)
    have he : (q/N)*(τ*(S.card:ℝ)*T.card/Nat.card K)=τ*T.card := by
      change (q/N)*(τ*N*T.card/q)=τ*T.card
      field_simp
    exact hh.trans_eq he
  obtain ⟨hE₀,hhalf,hE₀E,hsmallE⟩ := sparse_training S (fun _ : Unit => ∅) [] c T hT τ hτ
    (by linarith) htrain
  exact ⟨hsp,hBbig,hcsmall,hE₀,by linarith only [hhalf],hE₀E,hsmallE⟩

lemma training_size {q N t z : ℝ} (hN : 0<N) (hz : 0≤z) (b e : ℝ)
    (hprod : q^3*exp (-b)≤N*t) (hhalf : t≤2*z) :
    q*(q^2/N)*exp (-b-e)/8≤z*exp (-e)/2 := by
  have hTlow : q*(q^2/N)*exp (-b)≤t := by
    have he : q*(q^2/N)*exp (-b)=q^3*exp (-b)/N := by ring
    rw [he]
    apply (div_le_iff₀ hN).mpr
    simpa only [mul_comm] using hprod
  have he : exp (-b-e)=exp (-b)*exp (-e) := by
    simpa only [sub_eq_add_neg] using exp_add (-b) (-e)
  rw [he]
  have ht : q*(q^2/N)*exp (-b)≤2*z := hTlow.trans hhalf
  have hh := mul_le_mul_of_nonneg_right ht (exp_pos (-e)).le
  nlinarith only [hh,mul_nonneg hz (exp_pos (-e)).le]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
