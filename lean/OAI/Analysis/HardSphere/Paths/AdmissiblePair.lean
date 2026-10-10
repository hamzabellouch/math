import Mathlib
import OAI.Analysis.HardSphere.Geometry.PathEncounter

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

def admissiblePair {K : ℕ} [NeZero K] (x y : DiscreteTorus K) : Prop :=
  K≤4*(y 0-x 0).val ∧ 2*(y 0-x 0).val≤K

def admissiblePairs (K : ℕ) [NeZero K] : Finset (DiscreteTorus K × DiscreteTorus K) :=
  Finset.univ.filter (fun z ↦ admissiblePair z.1 z.2)

lemma admissible_lift {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
    (h : admissiblePair x y) :
    ∃ n : ℕ, 0<n ∧ 2*n≤K ∧ K≤4*n ∧ ∃ v : Vertex, ∃ Δ₂ Δ₃ : ℤ,
      |Δ₂|≤2*n ∧ |Δ₃|≤2*n ∧ torusProjection K v=x ∧
      torusProjection K (v+![(n:ℤ),Δ₂,Δ₃])=y := by
  have hK : 0<K := NeZero.pos K
  let n := (y 0-x 0).val
  let v : Vertex := fun i ↦ (x i).val
  let Δ₂ := (y 1-x 1).valMinAbs
  let Δ₃ := (y 2-x 2).valMinAbs
  have h₂ := ZMod.natAbs_valMinAbs_le (y 1-x 1)
  have h₃ := ZMod.natAbs_valMinAbs_le (y 2-x 2)
  have h₂' : |Δ₂|≤(K/2:ℕ) := by
    simpa only [Δ₂,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr h₂
  have h₃' : |Δ₃|≤(K/2:ℕ) := by
    simpa only [Δ₃,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr h₃
  have hnlow : K≤4*n := h.1
  refine ⟨n,by dsimp [n]; dsimp [admissiblePair] at h; omega,h.2,h.1,v,Δ₂,Δ₃,?_,?_,?_,?_⟩
  · have : (K/2:ℕ)≤2*n := by omega
    exact h₂'.trans (by exact_mod_cast this)
  · have : (K/2:ℕ)≤2*n := by omega
    exact h₃'.trans (by exact_mod_cast this)
  · funext i
    simp [torusProjection,v]
  · funext i
    fin_cases i <;> simp [torusProjection,v,n,Δ₂,Δ₃,ZMod.coe_valMinAbs]

lemma horizon_self (n : ℕ) : n/2≤3^n := by
  have : n≤3^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have : 0<3^n := by positivity
      omega
  exact (Nat.div_le_self _ _).trans this

theorem admissiblePairs_card {K : ℕ} [NeZero K] (hK : 8≤K) :
    K^6≤8*(admissiblePairs K).card := by
  let I := Finset.Icc (K/4+1) (K/2)
  let S : Finset (DiscreteTorus K × ℕ × ZMod K × ZMod K) :=
    Finset.univ ×ˢ (I ×ˢ (Finset.univ ×ˢ Finset.univ))
  let f : DiscreteTorus K × ℕ × ZMod K × ZMod K → DiscreteTorus K × DiscreteTorus K :=
    fun z ↦ (z.1,z.1+![(z.2.1:ZMod K),z.2.2.1,z.2.2.2])
  have hI (n : ℕ) (hn : n∈I) : K≤4*n ∧ 2*n≤K ∧ n<K := by
    have hn := Finset.mem_Icc.mp hn
    omega
  have hsub : S.image f⊆admissiblePairs K := by
    intro z hz
    obtain ⟨⟨x,n,b,c⟩,hu,rfl⟩ := Finset.mem_image.mp hz
    change (x,n,b,c)∈Finset.univ ×ˢ (I ×ˢ (Finset.univ ×ˢ Finset.univ)) at hu
    have hn := hI n (Finset.mem_product.mp (Finset.mem_product.mp hu).2).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [f,admissiblePair,Pi.add_apply,Matrix.cons_val_zero,add_sub_cancel_left,
      ZMod.val_natCast_of_lt hn.2.2]
    exact ⟨hn.1,hn.2.1⟩
  have hinj : Set.InjOn f (↑S : Set _) := by
    rintro ⟨x,n,b,c⟩ hx ⟨x',n',b',c'⟩ hx' he
    have he₁ : x=x' := congrArg Prod.fst he
    subst x'
    have he₂ : ![(n:ZMod K),b,c]=![(n':ZMod K),b',c'] := add_left_cancel (congrArg Prod.snd he)
    have hn := hI n (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    have hn' := hI n' (Finset.mem_product.mp (Finset.mem_product.mp hx').2).1
    have hnval := congrArg (fun z : Fin 3 → ZMod K ↦ (z 0).val) he₂
    simp only [Matrix.cons_val_zero,ZMod.val_natCast_of_lt hn.2.2,
      ZMod.val_natCast_of_lt hn'.2.2] at hnval
    have hb := congrFun he₂ 1
    have hc := congrFun he₂ 2
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero] at hb
    simp only [Matrix.cons_val_two] at hc
    simp only [Prod.mk.injEq]
    exact ⟨trivial,hnval,hb,hc⟩
  have hcard : S.card≤(admissiblePairs K).card :=
    (Finset.card_image_iff.mpr hinj).symm.trans_le (Finset.card_le_card hsub)
  have hcardS : S.card=K^3*I.card*K^2 := by
    simp [S,DiscreteTorus,Finset.card_product,ZMod.card,mul_assoc,pow_two]
  have hcardI : K≤8*I.card := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  rw [hcardS] at hcard
  calc
    K^6 = K^3*K*K^2 := by ring
    _ ≤ K^3*(8*I.card)*K^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcardI)
    _ = 8*(K^3*I.card*K^2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcard

theorem admissible_good_paths (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ, 0≤p → p≤p₀ → JointBadLaw μ (ENNReal.ofReal p) →
      ∀ x y : DiscreteTorus K, admissiblePair x y →
      ∃ E : Finset (DiscreteTorus K) → Prop,
      ∃ ν : (B : Finset (DiscreteTorus K)) → E B → PMF (SimpleGoodPath B x y),
        (1/2:ℝ≥0∞)≤(∑' B, if E B then μ B else 0) ∧
        (∑' B, μ B*(if hB : E B then pathKernelMoment R κ (ν B hB) else 0))≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := good_kernel_uniform_constants R
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst μ p hp hpp hbad x y hxy
  obtain ⟨n,hn,hnK,_,v,Δ₂,Δ₃,hΔ₂,hΔ₃,hv,hw⟩ := admissible_lift hxy
  subst x y
  obtain ⟨hK2,haccept,hmoment⟩ := hall K hK inst μ p hp hpp hbad n hn hnK n (horizon_self n)
    v Δ₂ Δ₃ hΔ₂ hΔ₃
  exact ⟨(fun B ↦ acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])),
    goodPathKernel hK2 R hn (horizon_self n) v Δ₂ Δ₃ hΔ₂ hΔ₃,haccept,hmoment⟩

end HardSphere.Lattice

end

end OAI
