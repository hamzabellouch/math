import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.ForwardPreparedStage
import OAI.Combinatorics.RamseyFive.Streams.HighThreePrepared

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

theorem eventually_prepared_dispatch {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c C Cm C₀ : ℝ) (hc : 0<c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
      (ctx : Ω→κ) (D B M k₀ : ℝ)
      (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (a : SlotClass),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→S.density≤C₀→8≤ m→
      σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
      (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
      (∀x,0 < map S.law ctx x→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain x i) a)→
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) ∨
      Nonempty (CodedStream (K:=K) (V:=Dual K V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_forward_prepared_stage hη hη' c C Cm hc hC hCm,
    eventually_no_high_class hη (c/8) C₀ (8*C) Cm (by positivity) (by positivity) hCm] with σ hf hh
  intro q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N m l adm S ctx D B M k₀ PS a
    hd hq3 hcard hσ hq hα hN hCs hm8 hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl
  rcases a with b|b|⟨r,s⟩
  · exact Or.inl (hf q₀ K V Ω κ α N m l adm S ctx D B M k₀ PS b
      hd hq3 hcard hσ hq hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl)
  · let : Fintype (ℙ K (Dual K (Dual K (Dual K V)))) :=
      Fintype.ofEquiv (ℙ K (Dual K V)) bidualPoint
    apply Or.inr
    apply hf q₀ K (Dual K V) Ω κ α N m l adm
      (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply)
      ctx D B M k₀ PS.swap b (by simpa using hd) hq3 hcard hσ hq hD hDhi
      hlen hm hl hk₀ hB hBhi hM hMhi
    intro c hc i
    obtain ⟨u,hu1,hu2,hu3,hu4⟩:=hcl c hc i.rev
    exact ⟨u,hu1,hu2,hu3.swap,hu4⟩
  · exfalso
    let t:=m/4
    have ht : 0<t := by dsimp [t];omega
    let : Nonempty (Fin t):=⟨⟨0,ht⟩⟩
    have htm : 1*(4*t)≤ m := by dsimp [t];omega
    have hmt : (m:ℝ)≤8*t := by exact_mod_cast (show m≤8*t by dsimp [t];omega)
    let e:=Fin.castLEOrderEmb htm
    have hJ : 4*σ≤Real.log (153*(Nat.card K:ℝ)^4) := by
      have hl153 : 0≤Real.log 153 := Real.log_nonneg (by norm_num)
      rw [Real.log_mul (by norm_num) (by rw [←hq];positivity),Real.log_pow,←hq,Real.log_exp]
      norm_num only [Nat.cast_ofNat]
      linarith
    have hDn : 0≤D := (Real.rpow_nonneg (by linarith : 0≤σ) _).trans hD
    have hB' : B≤8*C*(t:ℝ)*D*σ^(-beta η) := by
      have hmul:=mul_le_mul_of_nonneg_right hmt (by positivity : 0≤C*D*σ^(-beta η))
      nlinarith
    exact hh K V Ω κ α N t adm (S.reindex e) ctx D _ B M (D*σ^(3*beta η)) (PS.reindex e) r s
      hd hσ hq hα hN (by rw [hq];nlinarith) hCs hD hDhi hB' hMhi hJ
      (fun c hc i=>hcl c hc (e i))
end
end SharpRamseyFive.SelectedTuple

end OAI
