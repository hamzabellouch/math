import OAI.NumberTheory.DirichletL.Descent.CanonicalRankMonotone

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_rank_cap_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A Mnext Fnext cnext:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hMc:M-3*cutoff/2≤Mnext)(hFc:r+3*ell+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  exact canonical_rank_moments_children p hp hcop hg hc hpr pool Q k l j negative base Ψ hΨ m hm
    slots lists a ω₁ ω₂ Z M r ell V eta tau window b cutoff Qwidth z c eps A K degree
    hZ heta hbin hell hV hb hbt hwindow hd hterminal hsmall hparent hpuncture hQ
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₁ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₁)
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₂ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₂)

theorem canonical_depth_ceilings (n:ℕ)(cutoff Fbase cbase eta:ℝ)(M F c:ℝ)
    (hM:M≤3*(n:ℝ)*cutoff/2)(hF:F≤Fbase-15*(n:ℝ)*eta)
    (hc:cbase+7*((n:ℝ)+1)*eta≤c):
    M-3*cutoff/2≤3*((n:ℝ)-1)*cutoff/2 ∧
    F+15*eta≤Fbase-15*((n:ℝ)-1)*eta ∧
    cbase+7*(n:ℝ)*eta≤c-7*eta :=by
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI
