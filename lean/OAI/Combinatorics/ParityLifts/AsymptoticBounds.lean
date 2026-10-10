import OAI.Combinatorics.ParityLifts.UniformNormalization

namespace OAI

namespace ParityWL.Complexity

/-- Finite exceptional orders do not change a time bound for a total decider.
The bound is on actual executions, and no effective choice of constants is needed. -/
lemma extend_wl_time_bound (M : Machine) (header : List Bool) (c : Convention)
    (i : Implementation) (k : ℕ) (r C : ℝ) (hr : 0 ≤ r) (hC : 0<C) (N₀ : ℕ)
    (hTotal : ∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (header++encodeGraphs G H) s b ∧ (b=true↔Equivalent G H c i k))
    (hLarge : ∀ n : ℕ, N₀ ≤ n → ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (header++encodeGraphs G H) s b ∧ (b=true↔Equivalent G H c i k) ∧
      (s : ℝ) ≤ C*(n+1 : ℝ)^r) :
    ∃ D : ℝ, 0<D ∧ ∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (header++encodeGraphs G H) s b ∧ (b=true↔Equivalent G H c i k) ∧
      (s : ℝ) ≤ D*(n+1 : ℝ)^r := by
  classical
  let X := (n : Fin N₀) × (SimpleGraph (Fin n.val) × SimpleGraph (Fin n.val))
  have h : ∀ x : X, ∃ s b,
      Emits M (header++encodeGraphs x.2.1 x.2.2) s b ∧
      (b=true↔Equivalent x.2.1 x.2.2 c i k) :=
    fun x => hTotal x.1.val x.2.1 x.2.2
  choose times bits emits correct using h
  let B : ℕ := Finset.univ.sup times
  refine ⟨C+B+1,by positivity,?_⟩
  intro n G H
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hpow : 1 ≤ (n+1 : ℝ)^r := Real.one_le_rpow (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) hr
  by_cases hn : N₀ ≤ n
  · obtain ⟨s,b,hs,hb,ht⟩ := hLarge n hn G H
    refine ⟨s,b,hs,hb,ht.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · let x : X := ⟨⟨n,by omega⟩,G,H⟩
    refine ⟨times x,bits x,emits x,correct x,?_⟩
    have hx : times x ≤ B := Finset.le_sup (Finset.mem_univ x)
    have hx' : (times x : ℝ) ≤ B := by exact_mod_cast hx
    nlinarith

/-- The conventional big-O form: total correctness and one eventual n^r bound.
This allows arbitrary behavior at the finitely many smaller graph orders. -/
noncomputable def AsymptoticFixedWLBound (M : Machine) (c : Convention)
    (i : Implementation) (k : ℕ) (r : ℝ) : Prop :=
  (∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), ∃ s b,
    Emits M (encodeGraphs G H) s b ∧ (b=true↔Equivalent G H c i k)) ∧
  ∃ C : ℝ, 0<C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (encodeGraphs G H) s b ∧ (b=true↔Equivalent G H c i k) ∧
      (s : ℝ) ≤ C*(n : ℝ)^r

lemma AsymptoticFixedWLBound.fixed {M : Machine} {c : Convention} {i : Implementation}
    {k : ℕ} {r : ℝ} (h : AsymptoticFixedWLBound M c i k r) (hr : 0 ≤ r) :
    FixedWLBound M c i k r := by
  obtain ⟨htotal,C,hC,N₀,hlarge⟩ := h
  obtain ⟨D,hD,h⟩ := extend_wl_time_bound M [] c i k r C hr hC N₀
    (by simpa only [List.nil_append] using htotal) (by
      intro n hn G H
      obtain ⟨s,b,hs,hb,ht⟩ := hlarge n hn G H
      refine ⟨s,b,by simpa only [List.nil_append] using hs,hb,ht.trans ?_⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hr) hC.le)
  exact ⟨D,hD,by simpa only [List.nil_append] using h⟩

/-- O(n^(c*k)) exclusion, with arbitrary finite exceptional orders. -/
theorem fixed_dimension_eth_asymptotic (hETH : PositiveRateETH) :
    ∃ c : ℝ, 0<c ∧ ∃ K : ℕ, 4 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∀ conv : Convention, ∀ i : Implementation,
        ¬ ∃ M : Machine, AsymptoticFixedWLBound M conv i k (c*k) := by
  obtain ⟨c,hc,K,hK,h⟩ := fixed_dimension_eth hETH
  refine ⟨c,hc,K,hK,?_⟩
  intro k hk conv i hm
  obtain ⟨M,hM⟩ := hm
  exact h k hk conv i ⟨M,hM.fixed (by positivity)⟩

/-- Eventual time bounds may start at an arbitrary order depending on k; the
same finite machine receives binary k and the two full adjacency matrices. -/
noncomputable def AsymptoticUniformWLBound (M : Machine) (c : Convention)
    (i : Implementation) (f g : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    (∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (encodeNat k++encodeGraphs G H) s b ∧
      (b=true↔Equivalent G H c i k)) ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ G H : SimpleGraph (Fin n), ∃ s b,
      Emits M (encodeNat k++encodeGraphs G H) s b ∧
      (b=true↔Equivalent G H c i k) ∧ (s : ℝ) ≤ f k*(n : ℝ)^g k

/-- Uniform exclusion, even with arbitrary finite exceptions and
without any sign assumptions on f or g. No computable modulus is required. -/
theorem uniform_eth_asymptotic (hETH : UniformSubexponentialETH)
    (c : Convention) (i : Implementation) :
    ¬ ∃ (M : Machine) (f g : ℕ → ℝ),
      Filter.Tendsto (fun k : ℕ => g k/k) Filter.atTop (nhds 0) ∧
      AsymptoticUniformWLBound M c i f g := by
  classical
  intro h
  obtain ⟨M,f,g,hlim,hM⟩ := h
  have hbound : ∀ k : ℕ, ∃ D : ℝ, 0<D ∧ (4 ≤ k →
      ∀ n : ℕ, ∀ G H : SimpleGraph (Fin n), ∃ s b,
        Emits M (encodeNat k++encodeGraphs G H) s b ∧
        (b=true↔Equivalent G H c i k) ∧ (s : ℝ) ≤ D*(n+1 : ℝ)^|g k|) := by
    intro k
    by_cases hk : 4 ≤ k
    · obtain ⟨htotal,N₀,hlarge⟩ := hM k hk
      obtain ⟨D,hD,h⟩ := extend_wl_time_bound M (encodeNat k) c i k |g k| (|f k|+1)
        (abs_nonneg _) (by positivity) (max N₀ 1) htotal (by
          intro n hn G H
          obtain ⟨s,b,hs,hb,ht⟩ := hlarge n (le_max_left N₀ 1 |>.trans hn) G H
          refine ⟨s,b,hs,hb,ht.trans ?_⟩
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N₀ 1 |>.trans hn)
          calc
            f k*(n : ℝ)^g k ≤ (|f k|+1)*(n : ℝ)^g k :=
              mul_le_mul_of_nonneg_right (by linarith [le_abs_self (f k)])
                (Real.rpow_nonneg (Nat.cast_nonneg n) _)
            _ ≤ (|f k|+1)*(n : ℝ)^|g k| := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hn1 (le_abs_self _)) (by positivity)
            _ ≤ (|f k|+1)*(n+1 : ℝ)^|g k| := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) (abs_nonneg _)) (by positivity))
      exact ⟨D,hD,fun _ => h⟩
    · exact ⟨1,by norm_num,fun h => False.elim (hk h)⟩
  choose D hD hbound using hbound
  have hlim' : Filter.Tendsto (fun k : ℕ => |g k|/k) Filter.atTop (nhds 0) := by
    have hnat : ∀ k : ℕ, |(k : ℝ)|=k := fun k => abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [abs_div,hnat,abs_zero] using hlim.abs
  exact uniform_eth hETH c i ⟨M,D,(fun k => |g k|),hlim',hD,(fun k => abs_nonneg (g k)),hbound⟩

end ParityWL.Complexity

end OAI
