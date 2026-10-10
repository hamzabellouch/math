import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCost

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real
open scoped Classical BigOperators
noncomputable section
local instance flat_JoinedSpatialCostsActual_1 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Fin 4 → ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedSpatialCostsActual_2 (q : ℕ) [Fact q.Prime] : Finite (Module.Dual (ZMod q) (Fin 4 → ZMod q)) := Module.finite_of_finite (ZMod q)
local instance flat_JoinedSpatialCostsActual_3 (q : ℕ) [Fact q.Prime] : Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := Fintype.ofFinite _
local instance flat_JoinedSpatialCostsActual_4 (q : ℕ) [Fact q.Prime] : Finite (Submodule (ZMod q) (Fin 4 → ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4 → ZMod q) => (W:Set (Fin 4 → ZMod q))) SetLike.coe_injective

lemma prepared_cost (q : ℕ) [Fact q.Prime] (σ P τ dT : ℝ)
    (U : Finset (Projectivization (ZMod q) (Fin 4 → ZMod q))) (n : ℕ)
    (hq : 3≤q) (hex : exp σ=(q:ℝ)) (hn : 0<n) (hnu : n≤U.card)
    (hnup : (n:ℝ)≤2*(q:ℝ)^2) (hP : 1≤P) (hτ : τ≤1) (hdT : 0≤dT)
    (hbud : 40*σ*(⌈exp (7*σ/10)⌉₊+1:ℕ)≤(q:ℝ)) :
    let J := ⌈exp (7*σ/10)⌉₊
    let M := ⌈2*(q:ℝ)*P⌉₊
    let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
    let E := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+
      log ((Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)+1)
    ∀ (a : ℝ),0≤a → a≤(n+1:ℕ)*(J+1:ℕ)*
      ((Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))*(n+1)+1:ℕ):ℝ)^J*exp E →
    log (a+1)≤4000*((q:ℝ)*P*(log ((U.card:ℝ)/n)+dT+P)) := by
  dsimp only
  let d := log ((U.card:ℝ)/n)
  let Z := (q:ℝ)*P*(d+dT+P)
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hU : (0:ℝ)<U.card := hn'.trans_le (by exact_mod_cast hnu)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa only [one_mul] using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  let J := ⌈exp (7*σ/10)⌉₊
  let M := ⌈2*(q:ℝ)*P⌉₊
  let H := (Fintype.card (Projectivization (ZMod q) (Fin 4 → ZMod q)):ℝ)*log 2
  let QT := (Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))):ℝ)
  let N := Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))
  let Aheader := (n+1:ℕ)*(J+1:ℕ)*((N*(n+1)+1:ℕ):ℝ)^J
  let AE := 2*((M:ℝ)*log (2*U.card/n)+4*P*τ+log 4+log (H+1))+log 3+log (QT+1)
  have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
  have hcard : Nat.card (ZMod q)=q := by simp
  have hN : (N:ℝ)≤(q:ℝ)^16 := by
    have hh := DescriptionHeaders.card_submodule_le (K:=ZMod q) (V:=Fin 4 → ZMod q)
    rw [hdimm,hcard] at hh
    norm_num only [Nat.reducePow] at hh
    exact_mod_cast hh
  have hhead : log Aheader≤q := header_log_bound hq' hex hnup hN rfl hbud
  have hlogsplit : log (2*U.card/n)=log 2+d := by
    rw [show 2*(U.card:ℝ)/n=2*((U.card:ℝ)/n) by ring,log_mul (by norm_num) (by positivity)]
  have hH : log (H+1)≤4*(q:ℝ) := by simpa only [H,hcard] using (spatial_log_card hdimm).2
  have hQT : log (QT+1)≤4*(q:ℝ) := by
    simpa only [QT,hcard] using (spatial_log_card (V:=Module.Dual (ZMod q) (Fin 4 → ZMod q))
      (Subspace.dual_finrank_eq.trans hdimm)).1
  have hAE : AE≤300*Z := by
    have hc := spatial_cost (by linarith : (1:ℝ)≤q) hP hd hτ
      (Nat.ceil_lt_add_one (by positivity : 0≤2*(q:ℝ)*P)).le hH hQT
    dsimp only [AE]
    rw [hlogsplit]
    apply hc.trans
    change 300*(q:ℝ)*P*(d+P)≤300*((q:ℝ)*P*(d+dT+P))
    nlinarith [show 0≤(q:ℝ)*P*dT by positivity]
  intro a ha hAl
  have hh := cover_log_bound ha (by positivity : 0<Aheader) hAl (by positivity : 0≤301*Z)
    (show log Aheader+AE≤301*Z by linarith)
  change log (a+1)≤4000*Z
  linarith

lemma heavy_cost (q : ℕ) [Fact q.Prime] (P d dT : ℝ)
    (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q)))) (n : ℕ)
    (hq : 3≤q) (hnup : (n:ℝ)≤2*(q:ℝ)^2) (hP : 1≤P) (hd : 0≤d) (hdT : 0≤dT)
    (a : ℝ) (ha : 0≤a)
    (hab : a≤(Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q)):ℝ)*(q+1:ℕ)*(n+1:ℕ)*(UT.card+1:ℕ)*
      exp (4000*(q:ℝ)*P*(d+dT+P))) :
    log (a+1)≤4500*((q:ℝ)*P*(d+dT+P)) := by
  let Z := (q:ℝ)*P*(d+dT+P)
  let N := Nat.card (Submodule (ZMod q) (Fin 4 → ZMod q))
  have hq' : (3:ℝ)≤q := by exact_mod_cast hq
  have hqZ : (q:ℝ)≤Z := by
    calc
      _ ≤ (q:ℝ)*P := le_mul_of_one_le_right (by positivity) hP
      _ ≤ Z := le_mul_of_one_le_right (by positivity) (by linarith)
  have hZ : 1≤Z := by linarith
  have h2 : log (2:ℝ)≤1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hdimm : Module.finrank (ZMod q) (Fin 4 → ZMod q)=4 := by simp
  have hcard : Nat.card (ZMod q)=q := by simp
  have hN : (N:ℝ)≤(q:ℝ)^16 := by
    have hh := DescriptionHeaders.card_submodule_le (K:=ZMod q) (V:=Fin 4 → ZMod q)
    rw [hdimm,hcard] at hh
    norm_num only [Nat.reducePow] at hh
    exact_mod_cast hh
  have hUT : log (UT.card+1:ℕ)≤4*(q:ℝ) := by
    have hQT := (spatial_log_card (V:=Module.Dual (ZMod q) (Fin 4 → ZMod q))
      (Subspace.dual_finrank_eq.trans hdimm)).1
    rw [hcard] at hQT
    apply le_trans _ hQT
    apply log_le_log (by positivity)
    have hc : (UT.card:ℝ)≤Fintype.card (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4 → ZMod q))) := by
      exact_mod_cast card_le_univ UT
    push_cast
    linarith
  have hNpos : 0<N := Nat.card_pos
  have hBH : log ((N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ))≤24*(q:ℝ) :=
    heavy_header_cost hq' hNpos hN hnup hUT
  have hBbound : a≤(N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ)*exp (4000*Z) := by
    simpa only [Nat.cast_add,Nat.cast_one,N,Z,mul_assoc] using hab
  have hh := cover_log_bound ha
    (by positivity : 0<(N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ)) hBbound
    (by positivity : 0≤4024*Z) (show log ((N:ℝ)*((q:ℝ)+1)*(n+1:ℕ)*(UT.card+1:ℕ))+4000*Z≤4024*Z by linarith)
  change log (a+1)≤4500*Z
  linarith

end
end SharpLogRamsey.SpatialPublic

end

end OAI
