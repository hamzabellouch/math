import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalReassembly
import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailInfinite
import OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalLimit
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0

theorem physicalFrequency_finite
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m:=by
  rw [←finite_physical_reassembly p hp hcop hg hinj]
  unfold physicalFrequency
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    exact Finset.sum_comm
  · simp only [hd,ite_false,Finset.sum_const_zero]

theorem physicalFrequency_hasSum
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    HasSum (physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m)
      (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,∑'h:O,
          initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0):=by
  unfold physicalFrequency
  apply hasSum_sum
  intro G hG
  apply hasSum_sum
  intro U hU
  apply hasSum_sum
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    apply hasSum_sum
    intro E hE
    exact (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j marks W Φ hZ D m
      G U T E
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hd).hasSum
  · simpa only [hd,ite_false] using (hasSum_zero : HasSum (fun _ : O=>(0:ℂ)) 0)

theorem original_input_zero_nonzero
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    (∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg pool Ψ j 1 1
        (initialTest p marks W Z D) u‖^2:ℝ))=
    physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m 0+
      ∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
  rw [initial_input_physical p hp hcop hg hinj hc hpr pool Ψ j marks W Φ hZ D m]
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_eq_add_tsum_ite 0

theorem nonzero_frequency_norm_le
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m B:ℝ)(hZ:0<Z)
    (hfinite:∀freqT:Finset O,(0:O)∉freqT→
      ‖physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
        (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m‖≤B):
    ‖∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h‖≤B:=by
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  have hs0:Summable (fun h:O=>if h=0 then (0:ℂ) else
      physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h):=by
    apply (hs.summable.indicator {h:O|h≠0}).congr
    intro h
    by_cases he:h=0 <;> simp [Set.indicator,he]
  apply InverseInitialHighFrequencyTail.norm_tsum_of_finite_bound _ hs0
  intro T
  let freqT:=T.filter (fun h:O=>h≠0)
  have hzero:(0:O)∉freqT:=by simp [freqT]
  have he:(∑h∈T,if h=0 then (0:ℂ) else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
      ∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
    simp only [freqT,Finset.sum_filter,ite_not]
  rw [he,physicalFrequency_finite p hp hcop hg hinj]
  exact hfinite freqT hzero

end SevenEighths.InverseInitialPhysicalLimit

end

end OAI
