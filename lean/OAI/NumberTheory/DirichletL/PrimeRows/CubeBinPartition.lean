import OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]

end SevenEighths.ProbeHighRowFamily

end

end OAI
