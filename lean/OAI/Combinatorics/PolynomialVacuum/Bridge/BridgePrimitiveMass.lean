import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeWordMass

namespace OAI

namespace PolynomialVacuumBridge.Corridor.BridgeWord
open Filter
open scoped Topology
noncomputable instance : DecidableEq BridgeWord := Classical.decEq _
noncomputable def sequences (S : Finset BridgeWord) : ℕ → Finset (List BridgeWord)
  | 0 => {[]}
  | k+1 => ((S ×ˢ sequences S k).image (fun p => p.1::p.2))

theorem consPair_injective : Function.Injective (fun p : BridgeWord × List BridgeWord => p.1::p.2) := by
  intro p q h
  obtain ⟨h1,h2⟩ := List.cons.inj h
  exact Prod.ext h1 h2

theorem sequences_members (S : Finset BridgeWord) (k : ℕ) (L : List BridgeWord)
    (hL : L∈sequences S k) : ∀ A∈L,A∈S := by
  induction k generalizing L with
  | zero => simp only [sequences,Finset.mem_singleton] at hL; subst L; simp
  | succ k ih =>
    obtain ⟨⟨A,K⟩,hp,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hA,hK⟩ := Finset.mem_product.mp hp
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hA
    · exact ih K hK B hB

theorem sequence_height_bound (S : Finset BridgeWord) (H k : ℕ)
    (hS : ∀ A∈S,A.height≤H) (L : List BridgeWord) (hL : L∈sequences S k) :
    L.prod.height≤k*H := by
  induction k generalizing L with
  | zero => simp only [sequences,Finset.mem_singleton] at hL; subst L; simp
  | succ k ih =>
    obtain ⟨⟨A,K⟩,hp,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hA,hK⟩ := Finset.mem_product.mp hp
    have ha := hS A hA
    have hk := ih K hK
    simp only [List.prod_cons,height_mul,Nat.succ_mul]
    omega

theorem sequences_mass (S : Finset BridgeWord) (k : ℕ) :
    (∑ L∈sequences S k,mass L.prod)=(∑ A∈S,mass A)^k := by
  classical
  induction k with
  | zero => simp [sequences]
  | succ k ih =>
    rw [sequences,Finset.sum_image (fun _ _ _ _ h => consPair_injective h)]
    simp only [List.prod_cons,mass_mul,Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,ih,pow_succ']

theorem primitive_finite_sum_le_one (S : Finset BridgeWord) (hS : ∀ A∈S,A.IsPrimitive) :
    (∑ A∈S,mass A)≤1 := by
  classical
  let H := S.sup BridgeWord.height
  have hH : ∀ A∈S,A.height≤H := fun A hA => Finset.le_sup hA
  let a := ∑ A∈S,mass A
  have hb : ∀ k : ℕ,a^k≤ massConstant*((k : ℝ)*H+1) := by
    intro k
    let P := (sequences S k).image List.prod
    have hi : Set.InjOn (List.prod : List BridgeWord → BridgeWord) (sequences S k : Set (List BridgeWord)) := by
      intro L hL K hK hk
      exact primitive_factorization_unique L K (fun A hA => hS A (sequences_members S k L hL A hA))
        (fun A hA => hS A (sequences_members S k K hK A hA)) hk
    have he : a^k=∑ A∈P,mass A := by
      rw [Finset.sum_image hi,sequences_mass]
    rw [he]
    convert bounded_height_mass_bound (k*H) P ?_ using 1 <;> try simp [Nat.cast_mul]
    intro A hA
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hA
    exact sequence_height_bound S H k hH L hL
  by_contra hn
  have ha : 1<a := lt_of_not_ge hn
  have hzero : Tendsto (fun k : ℕ => (1 : ℝ)/a^k) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 ha
  have hone : Tendsto (fun k : ℕ => (k : ℝ)/a^k) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 ha
  have hlim := ((hone.mul_const (H : ℝ)).add hzero).const_mul massConstant
  have hineq : ∀ k : ℕ, 1≤ massConstant*((k : ℝ)/a^k*H+1/a^k) := by
    intro k
    have hp : 0<a^k := pow_pos (by linarith) _
    have := (le_div_iff₀ hp).mpr (show 1*a^k≤ massConstant*((k : ℝ)*H+1) by simpa using hb k)
    calc
      1 ≤ massConstant*((k : ℝ)*H+1)/a^k := this
      _ = massConstant*((k : ℝ)/a^k*H+1/a^k) := by ring
  have hbad := ge_of_tendsto hlim (Filter.Eventually.of_forall hineq)
  norm_num at hbad

abbrev Primitive := {A : BridgeWord // A.IsPrimitive}

theorem primitive_mass_summable : Summable (fun A : Primitive => mass A.val) := by
  refine summable_of_sum_le (c:=1) (fun A => (mass_pos A.val).le) ?_
  intro S
  rw [← Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
  exact primitive_finite_sum_le_one _ (by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact B.property)

theorem primitive_mass_le_one : (∑' A : Primitive,mass A.val)≤1 := by
  apply Real.tsum_le_of_sum_le (f := fun A : Primitive => mass A.val) (fun A => (mass_pos A.val).le)
  intro S
  rw [← Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
  exact primitive_finite_sum_le_one _ (by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
    exact B.property)

end PolynomialVacuumBridge.Corridor.BridgeWord

end OAI
