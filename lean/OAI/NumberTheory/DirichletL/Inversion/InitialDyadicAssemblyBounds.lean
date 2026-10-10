import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windows_card_log (a b:Fin 4→ℝ)(ha:∀i,0<a i)(hab:∀i,a i≤b i) :
    (Fintype.card (Windows a b):ℝ)≤∏i:Fin 4,(3+Real.logb 2 (b i/a i)) :=
  four_indices_card_bound a b ha hab

theorem windows_card_subpower (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀a b:Fin 4→ℝ,(∀i,0<a i)→(∀i,a i≤b i)→(∀i,b i/a i≤C*Z^R)→
        (Fintype.card (Windows a b):ℝ)≤A*Z^ε :=
  four_indices_subpower C R ε hC hR hε

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def windowBlock (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(k:Fin 4→ℤ) : ℂ :=
  physicalBlock p hp hcop hg
    (pointSource pool (windowSource p S cutoff Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))
    ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))∘erasePoint)
    Ψ j marks W₁ W₂ Φ Z D m

theorem physicalBlock_norm_le_windows
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (E:ℝ)(hblock:∀k:Windows a b,
      ‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
        (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_window_partition p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k:Windows a b,E := Finset.sum_le_sum (fun k hk=>hblock k)
    _ = _ := by simp

omit p hp hcop hg [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem physicalBlock_uniform_subpower
    (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀{κ:Type*}[DecidableEq κ](p:κ→Eis)(hp:∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (pool:Finset κ)(S:Finset (Source (ι:=κ) 0))
        (a b:Fin 4→ℝ),(∀i,0<a i)→(∀i,a i≤b i)→
        (∀i,b i/a i≤C*Z^R)→
        (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))→
      ∀(w:Source (ι:=κ) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset κ→ℂ)
        (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(D m E:ℝ),0≤E→
        (∀k:Windows a b,‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
          (fun i=>(k i).val)‖≤E)→
        ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
          Ψ j marks W₁ W₂ Φ Z D m‖≤A*Z^ε*E := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower C R ε hC hR hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hcount,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro κ _ p hp _ hcop hg pool S a b ha hab hr hs w Ψ j marks W₁ W₂ Φ D m E hE hb
  exact (physicalBlock_norm_le_windows p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ E hb).trans
    (mul_le_mul_of_nonneg_right (hc a b ha hab hr) hE)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
