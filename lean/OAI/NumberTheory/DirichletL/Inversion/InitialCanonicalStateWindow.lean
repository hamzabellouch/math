import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateSource

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_window_state
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ c₁ c₂:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (h₁:r+2*assignedCenter all z≤m-c₁)
    (h₂:2*r+8*assignedCenter all z≤3*m-c₂)
    (hc:0≤min c₁ c₂)(hηsmall:η≤min c₁ c₂/100)(hτ:τ≤min c₁ c₂/100)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryGenerator t≠0 ∧ 0≤N ∧ 0≤V ∧ 0≤M ∧
    0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    CanonicalMargins (N+V) M (fullPunctureWidth Z t j)
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2) ∧
    N+V≤r+assignedCenter all z+7*η ∧
    M≤r+assignedCenter all z+7*η ∧
    N+V-(N+(θ+v))=2*η := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hmg:=enlarged_initial_margins m r (assignedCenter all z) (assignedCenter assigned z)
    B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q)) c₁ c₂
    h₁ h₂ hreg.1 hP hQ hc hη hηsmall hτ (by simpa only [hD] using hcut)
  rw [←hD,hreg.2.2] at hmg
  have hactual:CanonicalMargins (max 0 (D-B-v)+(θ+v+2*η)) (θ+H+2*η)
      (fullPunctureWidth Z t (assignedElement assigned q))
      (assignedCenter (all\assigned) z+η) (min c₁ c₂/2):=by
    unfold CanonicalMargins at hmg ⊢
    constructor <;> linarith [hmg.1,hmg.2]
  have hF:max 0 (D-B-v)+(θ+v+2*η)≤r+assignedCenter all z+7*η:=by
    rw [hD] at hclip ⊢
    linarith [hreg.1]
  have hMF:θ+H+2*η≤max 0 (D-B-v)+(θ+v+2*η):=by
    have hh:=hactual.1
    linarith [hreg.2.1]
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hactual,hF,hMF.trans hF,by ring⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI
