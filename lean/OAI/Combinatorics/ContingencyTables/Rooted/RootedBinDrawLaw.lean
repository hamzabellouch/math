import OAI.Combinatorics.ContingencyTables.Rooted.RootedBinFramesProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleDraw

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

local instance freeCellDecidableEq (A : Instance (Fin m) (Fin n)) :
    DecidableEq (FreeCell A.small A.T) := by
  letI : DecidableEq (Fin m) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  infer_instance

abbrev FreeWords (A : Instance (Fin m) (Fin n)) (h : ℕ) :=
  (t : FreeCell A.small A.T) → Fin (offsetBitLength (freeRange A t) h A.d) → Bool

abbrev Words (A : Instance (Fin m) (Fin n)) (h : ℕ) :=
  (i : Fin (RootedCatalogGrid.freeCount A)) →
    Fin (offsetBitLength (freeRange A (RootedForestCatalog.freeEquiv A i)) h A.d) → Bool

def freeWordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    Words A h ≃ FreeWords A h :=
  Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    Fin (offsetBitLength (freeRange A t) h A.d) → Bool) (RootedForestCatalog.freeEquiv A)

def originalWordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    BinWords A h ≃ FreeWords A h :=
  Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    Fin (offsetBitLength (freeRange A t) h A.d) → Bool) (index A)

def reindexWords (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    Words A h ≃ BinWords A h :=
  (freeWordEquiv A h).trans (originalWordEquiv A h).symm

def wordBits (A : Instance (Fin m) (Fin n)) (h : ℕ) : ℕ :=
  ∑ i : Fin (RootedCatalogGrid.freeCount A),
    offsetBitLength (freeRange A (RootedForestCatalog.freeEquiv A i)) h A.d

def wordEquiv (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    (Fin (wordBits A h) → Bool) ≃ Words A h :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))

lemma wordBits_eq (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    wordBits A h=binWordBits A h := by
  unfold wordBits binWordBits
  apply Fintype.sum_equiv (RootedCatalogGrid.coordinateEquiv A)
  intro i
  simp only [RootedCatalogGrid.coordinateEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply]

def draw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Words A h) : FreeIndex A.small A.T A.b :=
  binWordDraw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h (reindexWords A h bits)

lemma draw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Words A h)) (draw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  have he := binWordDraw_law A K hK hW (RootedCatalogGrid.gridEquiv A K v) h
  unfold draw
  rw [←FairBits.map_equiv (reindexWords A h),FairBits.uniform_equiv]
  apply RationalLaw.ext
  funext f
  exact congrArg (fun p => p.mass f) he

private lemma interval_bits_le (K N beta h d : ℕ) (hK : 0 < K) (hN : 0 < N)
    (hb : beta < K) :
    offsetBitLength (intervalSize K N beta) h d ≤ offsetBitLength N h d := by
  simpa only [offsetBitLength,BinVectorProgram.activeWidth,BinVectorProgram.reservedWidth,
    BinIntervalProgram.intervalSize_eq] using
    BinVectorProgram.active_le_reserved K N beta h d hK hN hb

private lemma coordinate_scalar (K N beta h d : ℕ) (bits : List Bool) :
    BinVectorProgram.coordinate ((((K,N),beta),(h,d)),bits)=
      FairBits.endpoint K N beta+ProfilePrograms.scaledWordValue
        (intervalSize K N beta,bits.take (offsetBitLength (intervalSize K N beta) h d)) := by
  simp only [BinVectorProgram.coordinate,BinIntervalProgram.draw,BinIntervalProgram.endpoint_eq,
    BinIntervalProgram.intervalSize_eq,BinVectorProgram.activeWidth,offsetBitLength]

private lemma original_value (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K)
    (h : ℕ) (bits : FreeWords A h) (i : Fin (dimension A)) :
    (binWordDraw A K hK hW v h ((originalWordEquiv A h).symm bits) (index A i)).val=
      (intervalEquiv K (freeRange A (index A i)) (naturalBin A v (index A i))
        hK (Nat.succ_pos _) (naturalBin_lt A v _)
        (scaledBitInteger (binSize A K v i) (offsetBitLength (binSize A K v i) h A.d)
          (binSize_positive A K hK hW v i)
          (prefixWord (binBits_le A K hK v h i) (bits (index A i))))).val := by
  change ((Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
    {z : ℕ // z∈FairBits.fiber K (freeRange A t) (naturalBin A v t)}) (index A))
      (fun j => intervalEquiv K (freeRange A (index A j)) (naturalBin A v (index A j))
        hK (Nat.succ_pos _) (naturalBin_lt A v _)
        (scaledBitInteger (binSize A K v j) (offsetBitLength (binSize A K v j) h A.d)
          (binSize_positive A K hK hW v j)
          (prefixWord (binBits_le A K hK v h j)
            ((originalWordEquiv A h).symm bits j)))) (index A i)).val=_
  rw [Equiv.piCongrLeft_apply_apply]
  simp only [originalWordEquiv,Equiv.piCongrLeft_symm_apply]

private lemma original_free_value (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K)
    (h : ℕ) (bits : FreeWords A h) (t : FreeCell A.small A.T)
    (hsize : 0 < intervalSize K (freeRange A t) (naturalBin A v t)) :
    (binWordDraw A K hK hW v h ((originalWordEquiv A h).symm bits) t).val=
      (intervalEquiv K (freeRange A t) (naturalBin A v t)
        hK (Nat.succ_pos _) (naturalBin_lt A v t)
        (scaledBitInteger (intervalSize K (freeRange A t) (naturalBin A v t))
          (offsetBitLength (intervalSize K (freeRange A t) (naturalBin A v t)) h A.d)
          hsize (prefixWord (interval_bits_le K (freeRange A t)
            (naturalBin A v t) h A.d hK (Nat.succ_pos _) (naturalBin_lt A v t))
            (bits t)))).val := by
  obtain ⟨i,rfl⟩ := (index A).surjective t
  simpa only [binSize] using original_value A K hK hW v h bits i

lemma draw_coordinate (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Words A h) (i : Fin (RootedCatalogGrid.freeCount A)) :
    BinVectorProgram.coordinate
      ((((K,freeRange A (RootedForestCatalog.freeEquiv A i)),(v i).val.toNat),(h,A.d)),
        List.ofFn (bits i))=
      (draw A K hK hW v h bits (RootedForestCatalog.freeEquiv A i)).val := by
  let w := RootedCatalogGrid.gridEquiv A K v
  have hb : naturalBin A w (RootedForestCatalog.freeEquiv A i)=(v i).val.toNat := by
    simp only [w,naturalBin,RootedCatalogGrid.gridEquiv_free,Equiv.symm_apply_apply]
  have hp : 0 < intervalSize K (freeRange A (RootedForestCatalog.freeEquiv A i))
      (naturalBin A w (RootedForestCatalog.freeEquiv A i)) := by
    simpa only [binSize,Equiv.apply_symm_apply] using
      binSize_positive A K hK hW w ((index A).symm (RootedForestCatalog.freeEquiv A i))
  have hv := original_free_value A K hK hW w h (freeWordEquiv A h bits)
    (RootedForestCatalog.freeEquiv A i) hp
  let t := RootedForestCatalog.freeEquiv A i
  let M := intervalSize K (freeRange A t) (naturalBin A w t)
  let k := offsetBitLength M h A.d
  have hk : k ≤ offsetBitLength (freeRange A t) h A.d :=
    interval_bits_le K (freeRange A t) (naturalBin A w t) h A.d hK
      (Nat.succ_pos _) (naturalBin_lt A w t)
  have hs := ProfilePrograms.scaledWordValue_ofFn M k hp
    (prefixWord hk (freeWordEquiv A h bits t))
  change (draw A K hK hW v h bits t).val=FairBits.endpoint K (freeRange A t)
    (naturalBin A w t)+(scaledBitInteger M k hp
      (prefixWord hk (freeWordEquiv A h bits t))).val at hv
  rw [←hs,←BinVectorProgram.take_ofFn_prefix hk] at hv
  have hw : freeWordEquiv A h bits (RootedForestCatalog.freeEquiv A i)=bits i :=
    Equiv.piCongrLeft_apply_apply _ _ _ _
  dsimp only [t,M,k] at hv
  rw [hw] at hv
  rw [hb] at hv
  rw [coordinate_scalar]
  exact hv.symm

def flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (wordBits A h) → Bool) : FreeIndex A.small A.T A.b :=
  draw A K hK hW v h (wordEquiv A h bits)

theorem flatDraw_law (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (wordBits A h) → Bool)) (flatDraw A K hK hW v h)=
      approximateBinLaw A K hK hW (RootedCatalogGrid.gridEquiv A K v) h := by
  unfold flatDraw
  rw [←FairBits.map_equiv (wordEquiv A h),FairBits.uniform_equiv,draw_law]

theorem program_flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (wordBits A h) → Bool) :
    RootedBinFramesProgram.draw (RootedBinFramesProgram.data A h v,List.ofFn bits)=
      List.ofFn (fun i => (flatDraw A K hK hW v h bits
        (RootedForestCatalog.freeEquiv A i)).val) := by
  unfold RootedBinFramesProgram.draw
  rw [RootedBinFramesProgram.frames_data]
  let frames : Fin (RootedCatalogGrid.freeCount A) → BinVectorProgram.Frame := fun i =>
    (((K,freeRange A (RootedForestCatalog.freeEquiv A i)),(v i).val.toNat),(h,A.d))
  have he := BinVectorProgram.output_ofFn frames bits
  refine he.trans ?_
  apply congrArg List.ofFn
  funext i
  exact draw_coordinate A K hK hW v h (wordEquiv A h bits) i

end
end ContingencyTables.RootedBinDrawLaw

end OAI
