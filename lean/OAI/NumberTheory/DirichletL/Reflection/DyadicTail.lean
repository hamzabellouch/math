import OAI.NumberTheory.DirichletL.Reflection.FullDyadic

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

def rawDyadicLabel (x : RawTailIndex) : ℕ×ℕ×ℕ :=
  (x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val))

def rawDyadicCenter (scale : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  scale*(ramifiedScale 1 completedRamifiedStep i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3

lemma rawDyadicCenter_lower (scale : ℝ) (hs : 0≤scale) (x : RawTailIndex) :
    rawDyadicCenter scale (rawDyadicLabel x)/16 ≤
      scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3 := by
  exact dyadic_kernel_argument_lower scale 1 completedRamifiedStep hs (by norm_num)
    (le_trans zero_le_one completedRamifiedStep_gt_one.le) (rawDyadicLabel x)
    ⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩
    ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩

theorem tsum_cut_dyadic (f : RawTailIndex→ℂ) (cut : (ℕ×ℕ×ℕ)→Prop)
    (hf : Summable (fun x => if cut (rawDyadicLabel x) then f x else 0)) :
    (∑' x, if cut (rawDyadicLabel x) then f x else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
            ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0 := by
  rw [tsum_dualIdealDyads _ hf]
  apply tsum_congr
  intro i
  have hl (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
      rawDyadicLabel (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=i := by
    simp only [rawDyadicLabel,((mem_dualIdealDyad _ _).mp n.property).2,
      ((mem_dualIdealDyad _ _).mp b.property).2]
  by_cases hi : cut i
  · simp only [hl,ite_eq_left hi]
  · simp only [hl,ite_eq_right hi,Finset.sum_const_zero]

theorem literal_reflected_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤rawDyadicCenter scale i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm V scale 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0‖≤
        C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail (ι:=ι) (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro V hV G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI
