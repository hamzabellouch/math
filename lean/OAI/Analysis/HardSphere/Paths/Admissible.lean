import Mathlib
import OAI.Analysis.HardSphere.Paths.AcceptedIntegrand

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

def currentAdmissiblePair {K : ℕ} [NeZero K] (x y : DiscreteTorus K) : Prop :=
  ∃ n : ℕ, K≤10*n ∧ 8*n≤K ∧ ∃ d : Fin 2 → ℤ, (∀ j, |d j|≤n) ∧
    y=x+![(n:ZMod K),(d 0:ZMod K),(d 1:ZMod K)]

def currentAdmissiblePairs (K : ℕ) [NeZero K] : Finset (DiscreteTorus K × DiscreteTorus K) :=
  Finset.univ.filter (fun z ↦ currentAdmissiblePair z.1 z.2)

lemma current_admissible_lift {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
    (h : currentAdmissiblePair x y) :
    ∃ n : ℕ, 0<n ∧ 8*n≤K ∧ K≤10*n ∧ ∃ v : Vertex, ∃ d : Fin 2 → ℤ,
      (∀j, |d j|≤n) ∧ torusProjection K v=x ∧
      torusProjection K (v+![(n:ℤ),d 0,d 1])=y := by
  obtain ⟨n,hl,hu,d,hd,hy⟩ := h
  let v : Vertex := fun j ↦ (x j).val
  have hK : 0<K := NeZero.pos K
  refine ⟨n,by omega,hu,hl,v,d,hd,?_,?_⟩
  · ext j; simp [torusProjection,v]
  · rw [hy]
    ext j; fin_cases j <;> simp [torusProjection,v]

lemma current_admissible_card {K : ℕ} [NeZero K] (hK : 400≤K) :
    K^6≤2000*(currentAdmissiblePairs K).card := by
  let m := K/10
  let I := Finset.Icc (K/10+1) (K/8)
  let J := Finset.range (2*m+1)
  let S : Finset (DiscreteTorus K × ℕ × ℕ × ℕ) :=
    Finset.univ ×ˢ (I ×ˢ (J ×ˢ J))
  let f : DiscreteTorus K × ℕ × ℕ × ℕ → DiscreteTorus K × DiscreteTorus K :=
    fun z ↦ (z.1,z.1+![(z.2.1:ZMod K),((z.2.2.1:ℤ)-m:ZMod K),((z.2.2.2:ℤ)-m:ZMod K)])
  have hI (n : ℕ) (hn : n∈I) : K≤10*n ∧ 8*n≤K ∧ n<K ∧ m<n := by
    have hn := Finset.mem_Icc.mp hn
    dsimp [m]
    omega
  have hJ (b : ℕ) (hb : b∈J) : b<K ∧ |(b:ℤ)-m|≤(m:ℤ) := by
    have hb := Finset.mem_range.mp hb
    dsimp [m] at *
    constructor
    · omega
    · rw [abs_le]; constructor <;> omega
  have hsub : S.image f⊆currentAdmissiblePairs K := by
    intro z hz
    obtain ⟨⟨x,n,b,c⟩,hu,rfl⟩ := Finset.mem_image.mp hz
    simp only [S,Finset.mem_product] at hu
    obtain ⟨_,hn,hb,hc⟩ := hu
    have hin := hI n hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,n,hin.1,hin.2.1,![(b:ℤ)-m,(c:ℤ)-m],?_,?_⟩
    · intro j
      fin_cases j
      · exact (hJ b hb).2.trans (by exact_mod_cast hin.2.2.2.le)
      · exact (hJ c hc).2.trans (by exact_mod_cast hin.2.2.2.le)
    · simp [f]
  have hinj : Set.InjOn f (↑S : Set _) := by
    rintro ⟨x,n,b,c⟩ hx ⟨x',n',b',c'⟩ hx' he
    have he₁ : x=x' := congrArg Prod.fst he
    subst x'
    have he₂ : ![(n:ZMod K),((b:ℤ)-m:ZMod K),((c:ℤ)-m:ZMod K)]=
        ![(n':ZMod K),((b':ℤ)-m:ZMod K),((c':ℤ)-m:ZMod K)] :=
      add_left_cancel (congrArg Prod.snd he)
    change (x,n,b,c)∈S at hx
    change (x,n',b',c')∈S at hx'
    simp only [S,Finset.mem_product] at hx hx'
    obtain ⟨_,hn,hb,hc⟩ := hx
    obtain ⟨_,hn',hb',hc'⟩ := hx'
    have hnval := congrArg (fun z : Fin 3 → ZMod K ↦ (z 0).val) he₂
    simp only [Matrix.cons_val_zero,ZMod.val_natCast_of_lt (hI n hn).2.2.1,
      ZMod.val_natCast_of_lt (hI n' hn').2.2.1] at hnval
    have hbeq : (b:ZMod K)=(b':ZMod K) := by
      have h := congrFun he₂ 1
      simpa using h
    have hceq : (c:ZMod K)=(c':ZMod K) := by
      have h := congrFun he₂ 2
      simpa using h
    have hbval := congrArg ZMod.val hbeq
    have hcval := congrArg ZMod.val hceq
    simp only [ZMod.val_natCast_of_lt (hJ b hb).1,ZMod.val_natCast_of_lt (hJ b' hb').1] at hbval
    simp only [ZMod.val_natCast_of_lt (hJ c hc).1,ZMod.val_natCast_of_lt (hJ c' hc').1] at hcval
    simp only [Prod.mk.injEq]
    exact ⟨trivial,hnval,hbval,hcval⟩
  have hcard : S.card≤(currentAdmissiblePairs K).card :=
    (Finset.card_image_iff.mpr hinj).symm.trans_le (Finset.card_le_card hsub)
  have hcardS : S.card=K^3*I.card*J.card^2 := by
    dsimp only [S]
    rw [Finset.card_product,Finset.card_product,Finset.card_product]
    simp [DiscreteTorus,mul_assoc,pow_two]
  have hcardI : K≤50*I.card := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hcardJ : K≤6*J.card := by
    simp only [J,Finset.card_range,m]
    omega
  rw [hcardS] at hcard
  calc
    K^6=K^3*K*K^2 := by ring
    _ ≤ K^3*(50*I.card)*(6*J.card)^2 := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hcardI) (Nat.pow_le_pow_left hcardJ 2)
    _ = 1800*(K^3*I.card*J.card^2) := by ring
    _ ≤ 1800*(currentAdmissiblePairs K).card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

end HardSphere.DyadicSkeleton
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice

theorem current_good_paths (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      K^6≤2000*(currentAdmissiblePairs K).card ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω], ∀ P : Measure Ω, ∀ _ : IsProbabilityMeasure P,
      ∀ b : Ω → Finset (DiscreteTorus K), Measurable b →
      ∀ p : ℝ, 0≤p → p≤p₀ →
      (∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤(ENNReal.ofReal p)^A.card) →
      ∀ x y : DiscreteTorus K, currentAdmissiblePair x y →
      ∃ E : Set Ω, MeasurableSet E ∧ (1/2:ℝ≥0∞)≤P E ∧
      ∃ ν : Kernel Ω (SimplePath x y), IsMarkovKernel ν ∧
        (∀ e∈E, ν e {q | simplePathGood (b e) q}=1) ∧
        (∫⁻ e, E.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e ∂P)≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := dyadic_good_paths_lift R
  refine ⟨p₀,κ,hp₀,hκ,max K₀ 400,?_⟩
  intro K hK inst
  refine ⟨current_admissible_card ((le_max_right K₀ 400).trans hK),?_⟩
  intro Ω mΩ P hP b hb p hp hpp hbad x y hxy
  obtain ⟨n,hn,hnK,_,v,d,hd,hv,hw⟩ := current_admissible_lift hxy
  subst x y
  exact hall K ((le_max_left K₀ 400).trans hK) inst P hP b hb p hp hpp hbad n hn hnK d hd v

end HardSphere.DyadicSkeleton
end
end

end OAI
