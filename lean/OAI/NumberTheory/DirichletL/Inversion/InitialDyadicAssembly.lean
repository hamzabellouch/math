import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows
import OAI.NumberTheory.DirichletL.Moments.DyadicCount

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

abbrev Windows (a b : Fin 4→ℝ) := ∀ i:Fin 4,↥(indices (a i) (b i))

def exponent (Z:ℝ) (k:ℤ) : ℝ := Real.logb Z (dyadicScale k)

def cutoff : Fin 4→ℝ→ℂ := fun _ y=>(annulus y:ℂ)

def weight (k:Fin 4→ℤ) (q:Fin 4→ℝ) : ℂ :=
  ∏i:Fin 4,(dyadicWeight (k i) (q i):ℂ)

theorem exponent_scale (Z:ℝ) (hZ:1<Z) (k:ℤ) :
    Z^(exponent Z k)=dyadicScale k :=
  Real.rpow_logb (by positivity) (ne_of_gt hZ) (dyadicScale_pos k)

theorem weight_partition (a b q:Fin 4→ℝ) (ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    (∑k:Windows a b,weight (fun i=>(k i).val) q)=1 := by
  unfold weight
  rw [←Fintype.prod_sum (fun (i:Fin 4) (k:↥(indices (a i) (b i)))=>(dyadicWeight k.val (q i):ℂ))]
  have he (i:Fin 4) : (∑k:↥(indices (a i) (b i)),(dyadicWeight k.val (q i):ℂ))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun k=>(dyadicWeight k (q i):ℂ))]
    exact_mod_cast dyadic_partition_on_interval (a i) (b i) (q i) (ha i) (hq i)
  simp only [he,Finset.prod_const_one]

theorem weight_eq_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ) (q:Fin 6→ℝ) :
    weight k (fun i=>q (outerIndex i)) =
      outerCutoff cutoff (relativeNorm q Z D (exponent Z (k 0))
        (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))) := by
  simp [weight,Fin.prod_univ_succ,dyadicWeight,outerIndex,outerCutoff,cutoff,
    relativeNorm,secondRelativeNorm,exponent_scale Z hZ,mul_assoc]

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceNorms (x:Source (ι:=ι) 0) : Fin 4→ℝ :=
  fun i=>coordinates p (sourcePoint x ∅ ∅) (outerIndex i)

omit [DecidableEq ι] in
theorem source_weight_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ)
    (x:Source (ι:=ι) 0) :
    weight k (sourceNorms p x)=outerCutoff cutoff
      (sourceRelative p x Z D (exponent Z (k 0)) (exponent Z (k 2))
        (exponent Z (k 1)) (exponent Z (k 3))) :=
  weight_eq_cutoff Z D hZ k _

omit [DecidableEq ι] in
theorem sourceNorms_one_le (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal] (x:Source (ι:=ι) 0)
    (hf:x.frequency≠0) : ∀i,1≤sourceNorms p x i := by
  have hi (I:Ideal Eis) (hI:I≠0) : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · change 1≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hi _ (by change Ideal.span {x.frequency}≠⊥; exact Ideal.span_singleton_eq_bot.not.mpr hf)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*weight (fun i=>(k i).val) (sourceNorms p x))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨s,hsS,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply,erase_sourcePoint]
  rw [←Finset.sum_mul,←Finset.mul_sum,weight_partition a b _ ha (hs s hsS),mul_one]

theorem physicalBlock_window_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg
      (pointSource pool (windowSource p S cutoff Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))
      ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  rw [physicalBlock_partition p hp hcop hg pool S a b ha hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [source_weight_cutoff p Z D hZ]
  exact physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m w Ψ j marks W₁ W₂ Φ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
