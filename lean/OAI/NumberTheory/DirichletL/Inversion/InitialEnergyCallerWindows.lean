import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRanges
import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindows
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceRelative (x:Source (ι:=ι) 0)(Z D B v θ H:ℝ) : Fin 6→ℝ :=
  relativeNorm (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H

def windowSource (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H:ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>outerCutoff ψ (sourceRelative p x Z D B v θ H)≠0)

omit [DecidableEq ι] in
theorem sourceRelative_four (x:Source (ι:=ι) 0)(N M:Finset ι)
    (Z D B v θ H:ℝ)(i:Fin 4) :
    relativeNorm (coordinates p (sourcePoint x N M)) Z D B v θ H (InverseSecondChildWindows.outerIndex i)=
      sourceRelative p x Z D B v θ H (InverseSecondChildWindows.outerIndex i) := by
  fin_cases i <;> simp only [InverseSecondChildWindows.outerIndex,sourceRelative,relativeNorm,
    coordinates,sourcePoint,physicalCoordinates,secondRelativeNorm,Fin.castLE,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Matrix.cons_val_zero',Matrix.cons_val_succ']

theorem windowSource_four_nonzero
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ)
    {x:Point ι}(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H))(i:Fin 4) :
    ψ i (relativeNorm (coordinates p x) Z D B v θ H (InverseSecondChildWindows.outerIndex i))≠0 := by
  obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  have ho := (Finset.mem_filter.mp hs).2
  change outerCutoff ψ (sourceRelative p s Z D B v θ H)≠0 at ho
  rw [sourceRelative_four]
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  fin_cases i
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_windowSource
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)
    (Z D B v θ H m:ℝ)(w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ)) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (windowSource p S ψ Z D B v θ H))
      ((fun x=>w x*outerCutoff ψ (sourceRelative p x Z D B v θ H))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,windowSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ho:outerCutoff ψ (sourceRelative p x Z D B v θ H)=0
  · simp only [ho,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,erase_sourcePoint,
      mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left ho]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem actual_window_block_support
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)
    (a b A₀ B₀ A₂ B₂:ℝ)(hA₀:0<A₀)(hA₂:0<A₂)
    (hψ₀:∀y,ψ 0 y≠0→y∈Set.Icc A₀ B₀)
    (hψ₂:∀y,ψ 2 y≠0→y∈Set.Icc A₂ B₂)
    (hω₁:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₁ y=1)
    (hω₂:∀y∈Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)),ω₂ y=1)
    (hV:∀i y,0<y→ retainedCutoffs ψ ω₁ ω₂ i y≠0→V i (Real.log y)=1)
    (Z D B v θ H c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hW₁:Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Icc a b)
    (hW₂:Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Icc a b) :
    BlockSupport p (pointSource pool (windowSource p S ψ Z D B v θ H))
      W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ := by
  have hvalid : ∀x∈pointSource pool (windowSource p S ψ Z D B v θ H),Valid x :=
    pointSource_valid pool _ (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
      (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
  have hpos (x:Point ι)(hx:x∈pointSource pool (windowSource p S ψ Z D B v θ H)) :
      ∀i,0<relativeNorm (coordinates p x) Z D B v θ H i :=
    relativeNorm_pos _ (coordinates_pos p hp x (hvalid x hx)) hZ D B v θ H
  refine ⟨?_,?_,?_⟩
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₁ c₁ θ₁) ω₁ a b A₀ B₀ A₂ B₂
      _ _ _ hW₁ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 4).le hω₁ hlive
    rw [relative_column_left] at he
    rw [he,star_one]
  · intro x hx hlive
    have he := fresh_window_eq_one (clippedSource W₂ c₂ θ₂) ω₂ a b A₀ B₀ A₂ B₂
      _ _ _ hW₂ hA₀ hA₂
      (hψ₀ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0))
      (hψ₂ _ (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
      (hpos x hx 5).le hω₂ hlive
    rwa [relative_column_right] at he
  · intro x hx h₁ h₂ i
    apply hV i _ (hpos x hx i)
    apply retainedCutoffs_nonzero ψ ω₁ ω₂ _ ?_ ?_ ?_ i
    · unfold outerCutoff
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 0)
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 1))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 2))
        (windowSource_four_nonzero p pool S ψ Z D B v θ H hx 3)
    · rw [relative_column_left]
      exact star_ne_zero.mp h₁
    · rwa [relative_column_right]

end SevenEighths.InverseInitialEnergyCallerWindows

end

end OAI
