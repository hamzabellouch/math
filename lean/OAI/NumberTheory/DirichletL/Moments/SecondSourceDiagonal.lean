import OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy
import OAI.NumberTheory.DirichletL.Moments.CommonRadialData
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondSourceDiagonal
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceSecondZeroEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentOriginalCommonHarmonic
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem actual_second_zero (N:ℕ)(ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N →
      ∀(a b:ℝ),0<a → 0≤b → ∀(s:Input ι)(p:Profiles a b),
      s.W₁=p.profile 0 → s.W₂=p.profile 1 → ∀(R seed:Ideal O),seed≠0 →
      ∀κ:ℂ,
      ‖κ*sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) s.η s.t‖/volume s.toData≤
      C*‖κ‖*(2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*
        (∏i,s.M i))^2*(1+(∏i,max 0 (s.hi i))*b*b)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=profile_second_zero_energy N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ _ hcard a b ha hb s p hw1 hw2 R seed hseed κ
  have hM (i:ι):0≤s.M i:=zero_le_one.trans (s.M_ge_one i)
  have hhi (i:ι):0≤max 0 (s.hi i):=le_max_left _ _
  have hz (i:Fin 2):p.profile i 0=0:=by
    by_contra hn
    exact (not_le_of_gt ha) (p.support i hn).1
  have hslotzero (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hW1:∀x,‖s.W₁ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 0):=by
    intro x;rw [hw1];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hW2:∀x,‖s.W₂ x‖≤SchwartzMap.seminorm ℝ 0 0 (p.profile 1):=by
    intro x;rw [hw2];exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hh:=(hbound hcard s.η s.t R s.ν s.ν_bound s.W s.P s.M (fun i=>max 0 (s.hi i)) s.W₁ s.W₂
    (SchwartzMap.seminorm ℝ 0 0 (p.profile 0)) (SchwartzMap.seminorm ℝ 0 0 (p.profile 1)) b b
    hM (apply_nonneg _ _) (apply_nonneg _ _) hhi hb hb s.W_bound hW1 hW2
    hslotzero (by rw [hw1];exact hz 0) (by rw [hw2];exact hz 1)
    (fun i x hx=>((s.support i hx).2).trans (le_max_right _ _))
    (by intro x hx;rw [hw1] at hx;exact (p.support 0 hx).2)
    (by intro x hx;rw [hw2] at hx;exact (p.support 1 hx).2)
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero hseed rfl s.same_product (Fintype.piFinset s.pools)).2 κ
  have hV:=volume_pos s.toData
  simpa only [map_one,Nat.cast_one,mul_one,div_one,coefficient,volume,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hV,abs_of_pos s.X₁_pos,abs_of_pos s.X₂_pos,
    abs_of_pos (Finset.prod_pos (fun i _=>s.P_pos i)),mul_div_assoc,div_mul_eq_mul_div] using hh

end SevenEighths.CenteredMomentSecondSourceDiagonal

end

end OAI
