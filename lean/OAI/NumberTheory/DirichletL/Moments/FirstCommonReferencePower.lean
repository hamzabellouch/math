import OAI.NumberTheory.DirichletL.Moments.FirstCommonSourcePowerBudget
import OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonReferencePower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstCommonSourcePowerBudget
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def normalizedPower (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ):ℝ:=
  C^ε*(b^N)^α*E/q*(V/C)^(α-1)*Z^(-allowance)

lemma normalizedPower_nonneg (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0≤b)(hV:0≤V)(hC:0≤C)(hq:0≤q)(hZ:0≤Z)(hE:0≤E):
    0≤normalizedPower b V C q Z allowance ε E N α:=by
  unfold normalizedPower
  positivity

lemma reference_power_identity (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0<b)(hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    (q*(V/C)^2*Z^allowance)*normalizedPower b V C q Z allowance ε E N α=
      C^(ε-1)*V*E*(b^N*V/C)^α:=by
  have hx:0<V/C:=div_pos hV hC
  have hbN:0<b^N:=pow_pos hb N
  have hprod:Z^allowance*Z^(-allowance)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  unfold normalizedPower
  rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_sub hC,Real.rpow_one,
    show b^N*V/C=b^N*(V/C) by ring,Real.mul_rpow hbN.le hx.le]
  field_simp
  calc
    _ = E*(Z^allowance*Z^(-allowance)):=by ring
    _ = E:=by rw [hprod,mul_one]

theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0<K→0<Z→
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*volume s*E j*
        (b^N*volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring

end SevenEighths.CenteredMomentFirstCommonReferencePower

end

end OAI
